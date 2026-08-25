#!/usr/bin/env python3
"""Independent arbitrary-precision audit of the recursive Harman certificate.

This implementation does not invoke or parse the C++ executable.  It uses
Python integers throughout and a sweep-line weighted-interval algorithm,
whereas the C++ certificate scans all active intervals on every component.

The canonical proof grid is

    python3 scripts/audit_harman_recursive_tail.py \
        1200 300 160 --workers 16

Use ``--dump-cells`` in both implementations to compare every alpha-cell
tuple ``(saving, tail, A3)`` exactly.
"""

from __future__ import annotations

import argparse
import heapq
import multiprocessing as mp
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Iterable


SCALE = 10**12
OMEGA_UPPER = 561_700_000_000
OMEGA_LOWER = 560_700_000_000
HALF = SCALE // 2
TARGET = 32_000_000_000


def floor_scaled(num: int, den: int) -> int:
    if num < 0 or den <= 0:
        raise ValueError("floor_scaled expects nonnegative input")
    return SCALE * num // den


def ceil_scaled(num: int, den: int) -> int:
    if num < 0 or den <= 0:
        raise ValueError("ceil_scaled expects nonnegative input")
    return (SCALE * num + den - 1) // den


def mul_down(x: int, y: int) -> int:
    if x < 0 or y < 0:
        raise ValueError("mul_down expects nonnegative input")
    return x * y // SCALE


def mul_up(x: int, y: int) -> int:
    if x < 0 or y < 0:
        raise ValueError("mul_up expects nonnegative input")
    return (x * y + SCALE - 1) // SCALE


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int
    weight: int


@dataclass(frozen=True)
class Cell:
    lo: int
    hi: int


@dataclass(frozen=True)
class AlphaBounds:
    alpha_lo: int
    alpha_hi: int
    gamma_min: int
    gamma_max: int
    tau_max: int
    a_min: int
    a_max: int
    sigma_min: int
    xi_min: int


@dataclass(frozen=True)
class CellResult:
    saving: int
    tail: int
    a3: int


def threshold_table() -> tuple[tuple[int, int, int], ...]:
    raw = (
        (201, 100), (21, 10), (11, 5), (23, 10), (12, 5), (5, 2),
        (13, 5), (27, 10), (14, 5), (29, 10), (3, 1), (31, 10),
        (16, 5), (33, 10), (17, 5), (7, 2), (18, 5), (37, 10),
        (19, 5), (39, 10), (4, 1),
    )
    return tuple(
        (p, q, floor_scaled(4 * (p - 2 * q) * q, p * p))
        for p, q in raw
    )


THRESHOLDS = threshold_table()


def add_interval(
    out: list[Interval], lo: int, hi: int, weight: int,
    domain_lo: int, domain_hi: int,
) -> None:
    lo = max(lo, domain_lo)
    hi = min(hi, domain_hi)
    if lo < hi and weight > 0:
        out.append(Interval(lo, hi, weight))


def weighted_reciprocal_lower(intervals: Iterable[Interval], den: int) -> int:
    """Sweep-line lower bound for integral max(weight) db/b^2."""
    starts: dict[int, list[int]] = defaultdict(list)
    ends: dict[int, list[int]] = defaultdict(list)
    points: set[int] = set()
    for interval in intervals:
        starts[interval.lo].append(interval.weight)
        ends[interval.hi].append(interval.weight)
        points.add(interval.lo)
        points.add(interval.hi)
    if len(points) < 2:
        return 0

    ordered = sorted(points)
    counts: Counter[int] = Counter()
    heap: list[int] = []
    answer = 0
    for pos, nxt in zip(ordered, ordered[1:]):
        for weight in ends.get(pos, ()):
            counts[weight] -= 1
        for weight in starts.get(pos, ()):
            counts[weight] += 1
            heapq.heappush(heap, -weight)
        while heap and counts[-heap[0]] <= 0:
            heapq.heappop(heap)
        if not heap or not (0 < pos < nxt):
            continue
        weight = -heap[0]
        left = floor_scaled(den, pos)
        right = ceil_scaled(den, nxt)
        if left > right:
            answer += mul_down(left - right, weight)
    return answer


def third_prime_intervals(
    b1: Cell, b2: Cell, domain_lo: int, domain_hi: int,
    a_max: int, sigma_min: int, half: int,
) -> list[Interval]:
    out: list[Interval] = []
    if not domain_lo < domain_hi:
        return out

    if a_max <= b1.lo + b2.lo and b1.hi + b2.hi <= sigma_min:
        add_interval(out, domain_lo, domain_hi, OMEGA_LOWER,
                     domain_lo, domain_hi)
    else:
        add_interval(out, a_max - b1.lo, sigma_min - b1.hi,
                     OMEGA_LOWER, domain_lo, domain_hi)
        add_interval(out, a_max - b2.lo, sigma_min - b2.hi,
                     OMEGA_LOWER, domain_lo, domain_hi)
        add_interval(out, a_max - b1.lo - b2.lo,
                     sigma_min - b1.hi - b2.hi,
                     OMEGA_LOWER, domain_lo, domain_hi)

    residual = half - b1.hi - b2.hi
    if residual > 0:
        for p, q, weight in THRESHOLDS:
            upper = q * residual // (p + q)
            add_interval(out, domain_lo, upper, weight,
                         domain_lo, domain_hi)
    return out


def alpha_bounds(index: int, steps: int) -> AlphaBounds:
    lo_num = 14 * steps + index
    hi_num = lo_num + 1
    return AlphaBounds(
        alpha_lo=floor_scaled(lo_num, 12 * steps),
        alpha_hi=ceil_scaled(hi_num, 12 * steps),
        gamma_min=floor_scaled(60 * steps - 4 * hi_num, 36 * steps),
        gamma_max=ceil_scaled(60 * steps - 4 * lo_num, 36 * steps),
        tau_max=ceil_scaled(18 * steps - lo_num, 24 * steps),
        a_min=floor_scaled(lo_num - 12 * steps, 12 * steps),
        a_max=ceil_scaled(hi_num - 12 * steps, 12 * steps),
        sigma_min=floor_scaled(24 * steps - hi_num, 36 * steps),
        xi_min=floor_scaled(18 * steps - hi_num, 12 * steps),
    )


def equal_cell(lo: int, hi: int, index: int, steps: int) -> Cell:
    width = hi - lo
    return Cell(lo + width * index // steps,
                lo + width * (index + 1) // steps)


def pair_child_upper(ab: AlphaBounds, b1: Cell, b2: Cell) -> int | None:
    if not (0 < b2.lo < b2.hi):
        return None
    selected_hi = b1.hi + b2.hi
    delta_min = HALF - selected_hi
    if delta_min <= 0:
        return None

    by_delta = ceil_scaled(2 * SCALE, delta_min)
    by_beta = ceil_scaled(2 * SCALE, 3 * b2.lo)
    best = max(by_delta, by_beta)

    if ab.a_max <= b1.lo + b2.lo and b1.hi + b2.hi <= ab.sigma_min:
        return min(best, ceil_scaled(OMEGA_UPPER, b2.lo))

    if selected_hi <= ab.xi_min and ab.gamma_min > 0:
        base_upper = ceil_scaled(OMEGA_UPPER, ab.gamma_min)
        if ab.gamma_max < b2.lo:
            intervals = third_prime_intervals(
                b1, b2, ab.gamma_max, b2.lo,
                ab.a_max, ab.sigma_min, HALF,
            )
            children_lower = weighted_reciprocal_lower(intervals, SCALE)
            if children_lower <= base_upper:
                best = min(best, base_upper - children_lower)
    return best


def tail_lower(ab: AlphaBounds, steps: int) -> int:
    if not (0 < ab.gamma_min and ab.tau_max < ab.a_min):
        return 0
    answer = 0
    for i1 in range(steps):
        b1 = equal_cell(ab.tau_max, ab.a_min, i1, steps)
        if not (0 < b1.lo < b1.hi):
            continue
        base_lower = floor_scaled(OMEGA_LOWER, ab.gamma_max)
        children_upper = 0
        valid = True
        for i2 in range(steps):
            b2 = equal_cell(ab.gamma_min, b1.hi, i2, steps)
            upper = pair_child_upper(ab, b1, b2)
            if upper is None:
                valid = False
                break
            log_upper = ceil_scaled(b2.hi - b2.lo, b2.lo)
            children_upper += mul_up(upper, log_upper)
        if not valid or base_lower <= children_upper:
            continue
        node_lower = base_lower - children_upper
        log_lower = floor_scaled(b1.hi - b1.lo, b1.hi)
        answer += mul_down(mul_down(ab.alpha_lo, node_lower), log_lower)
    return answer


def certify_cell(task: tuple[int, int, int, int]) -> CellResult:
    index, alpha_steps, beta_steps, tail_steps = task
    n = alpha_steps
    b = beta_steps
    lo_num = 14 * n + index
    hi_num = lo_num + 1
    if 100 * lo_num >= 122 * 12 * n or index == n - 1:
        return CellResult(0, 0, 0)

    den = 72 * n * b
    common_width = 4 * n + 5 * index - 3
    containing_width = 4 * n + 5 * index + 8
    if common_width <= 0:
        return CellResult(0, 0, 0)

    def common(k: int) -> int:
        return 8 * b * (n - index) + k * common_width

    def containing(k: int) -> int:
        return 8 * b * (n - index - 1) + k * containing_width

    alpha_gamma_up = ceil_scaled(3 * hi_num, 4 * (n - index - 1))
    a0_upper = mul_up(OMEGA_UPPER, alpha_gamma_up)

    common_log_lower = sum(
        floor_scaled(common_width, common(k)) for k in range(1, b + 1)
    )
    alpha_gamma_down = floor_scaled(3 * lo_num, 4 * (n - index))
    a1_lower = mul_down(mul_down(OMEGA_LOWER, alpha_gamma_down),
                        common_log_lower)

    containing_log_upper = sum(
        ceil_scaled(containing_width, containing(k)) for k in range(b)
    )
    a2_upper = mul_up(mul_up(OMEGA_UPPER, alpha_gamma_up),
                      mul_up(containing_log_upper, containing_log_upper))
    a2_upper = (a2_upper + 1) // 2

    type_lo = (2 * n + index + 1) * 6 * b
    type_hi = (10 * n - index - 1) * 2 * b
    gamma = common(0)
    alpha_lo = floor_scaled(lo_num, 12 * n)
    width_down = floor_scaled(common_width, den)
    width_sq = mul_down(width_down, width_down)
    triple = 0

    for i1 in range(1, b):
        b1 = Cell(common(i1), common(i1 + 1))
        row = 0
        for i2 in range(1, i1):
            b2 = Cell(common(i2), common(i2 + 1))
            intervals = third_prime_intervals(
                b1, b2, gamma, b2.lo, type_lo, type_hi, den // 2,
            )
            beta3 = weighted_reciprocal_lower(intervals, den)
            reciprocal_b1b2 = floor_scaled(
                den * den, b1.hi * b2.hi,
            )
            row += mul_down(beta3, reciprocal_b1b2)
        triple += mul_down(width_sq, row)
    a3_lower = mul_down(alpha_lo, triple)

    ab = alpha_bounds(index, alpha_steps)
    tail = tail_lower(ab, tail_steps)
    linear = floor_scaled(4 * lo_num, 12 * n)
    switched_upper = a0_upper - a1_lower + a2_upper - a3_lower - tail
    return CellResult(max(0, linear - switched_upper), tail, a3_lower)


def decimal(value: int) -> str:
    return f"{value // SCALE}.{value % SCALE:012d}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("alpha_steps", type=int, nargs="?", default=600)
    parser.add_argument("beta_steps", type=int, nargs="?", default=160)
    parser.add_argument("tail_beta_steps", type=int, nargs="?", default=80)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--dump-cells", action="store_true")
    args = parser.parse_args()
    if (args.alpha_steps <= 1 or args.beta_steps <= 4 or
            args.tail_beta_steps <= 4 or args.workers <= 0):
        parser.error("grid sizes and worker count must be positive")

    tasks = (
        (i, args.alpha_steps, args.beta_steps, args.tail_beta_steps)
        for i in range(args.alpha_steps)
    )
    if args.workers == 1:
        results = list(map(certify_cell, tasks))
    else:
        with mp.Pool(args.workers) as pool:
            results = list(pool.imap(certify_cell, tasks, chunksize=1))

    if args.dump_cells:
        for i, result in enumerate(results):
            print(f"cell={i},saving={result.saving},tail={result.tail},a3={result.a3}")

    saving = sum(result.saving for result in results) // (12 * args.alpha_steps)
    tail = sum(result.tail for result in results) // (12 * args.alpha_steps)
    a3 = sum(result.a3 for result in results) // (12 * args.alpha_steps)
    positive = sum(result.saving > 0 for result in results)

    print(f"scale={SCALE}")
    print(f"alpha_steps={args.alpha_steps} beta_steps={args.beta_steps} "
          f"tail_beta_steps={args.tail_beta_steps}")
    print(f"positive_alpha_cells={positive}")
    print(f"tail_lower_integral={decimal(tail)}")
    print(f"a3_lower_integral={decimal(a3)}")
    print(f"saving_lower_units={saving}")
    print(f"saving_lower={decimal(saving)}")
    print(f"target={decimal(TARGET)}")
    print(f"CERTIFIED={'YES' if saving > TARGET else 'NO'}")
    return 0 if saving > TARGET else 1


if __name__ == "__main__":
    raise SystemExit(main())
