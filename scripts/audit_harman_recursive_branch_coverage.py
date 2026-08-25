#!/usr/bin/env python3
"""Exhaustive branch-coverage audit for the canonical recursive certificate.

This script does not recompute the saving.  It checks that every analytic
branch selected by the 1200 x 300 x 160 certificate satisfies the uniform
exponent gate claimed in the manuscript.  All comparisons use integers;
no floating-point arithmetic is involved.
"""

from __future__ import annotations

from dataclasses import dataclass

from audit_harman_recursive_tail import SCALE, alpha_bounds


@dataclass
class MinimumRatio:
    numerator: int | None = None
    denominator: int = 1

    def include(self, numerator: int, denominator: int) -> None:
        if numerator < 0 or denominator <= 0:
            raise ValueError("ratio inputs must be nonnegative")
        if (self.numerator is None or
                numerator * self.denominator < self.numerator * denominator):
            self.numerator = numerator
            self.denominator = denominator

    def at_least(self, numerator: int, denominator: int) -> bool:
        return (self.numerator is not None and
                self.numerator * denominator >= numerator * self.denominator)

    def decimal(self, places: int = 9) -> str:
        if self.numerator is None:
            return "n/a"
        scale = 10**places
        value = self.numerator * scale // self.denominator
        return f"{value // scale}.{value % scale:0{places}d}"


def clipped(lo: int, hi: int, domain_lo: int, domain_hi: int) -> tuple[int, int] | None:
    lo = max(lo, domain_lo)
    hi = min(hi, domain_hi)
    return (lo, hi) if lo < hi else None


def main() -> int:
    alpha_steps = 1200
    a3_steps = 300
    tail_steps = 160

    # alpha = 7/6 + i/(12*n); alpha=1.22 occurs exactly at i=768.
    cutoff_index = 768
    assert 100 * (14 * alpha_steps + cutoff_index) == 122 * 12 * alpha_steps

    retained_alpha_cells = 0
    a3_boxes = 0
    a3_type_ii_boxes = 0
    a3_lower_sieve_boxes = 0
    a3_type_ii_intervals = 0
    tail_nodes = 0
    tail_pair_boxes = 0
    tail_invalid_pair_boxes = 0
    tail_linear_sieve_boxes = 0
    tail_type_ii_boxes = 0
    tail_recursive_boxes = 0
    tail_linear_only_boxes = 0

    a3_omega_argument = MinimumRatio()
    tail_base_argument = MinimumRatio()
    pair_type_ii_argument = MinimumRatio()
    recursive_base_argument = MinimumRatio()

    for i in range(alpha_steps):
        alpha_lo_num = 14 * alpha_steps + i
        if 100 * alpha_lo_num >= 122 * 12 * alpha_steps:
            continue
        retained_alpha_cells += 1

        # Main A3 grid.  Every exponent has denominator 72*n*b.
        n = alpha_steps
        b = a3_steps
        den = 72 * n * b
        common_width = 4 * n + 5 * i - 3
        common = lambda k: 8 * b * (n - i) + k * common_width
        domain_lo = common(0)
        half = den // 2
        a_max = (2 * n + i + 1) * 6 * b
        sigma_min = (10 * n - i - 1) * 2 * b
        alpha_lo = alpha_lo_num * 6 * b

        for i1 in range(1, b):
            b1_lo = common(i1)
            b1_hi = common(i1 + 1)
            for i2 in range(1, i1):
                a3_boxes += 1
                b2_lo = common(i2)
                b2_hi = common(i2 + 1)
                domain_hi = b2_lo
                type_ii_intervals: list[tuple[int, int]] = []

                if a_max <= b1_lo + b2_lo and b1_hi + b2_hi <= sigma_min:
                    interval = clipped(domain_lo, domain_hi, domain_lo, domain_hi)
                    if interval:
                        type_ii_intervals.append(interval)
                else:
                    for lo, hi in (
                        (a_max - b1_lo, sigma_min - b1_hi),
                        (a_max - b2_lo, sigma_min - b2_hi),
                        (a_max - b1_lo - b2_lo,
                         sigma_min - b1_hi - b2_hi),
                    ):
                        interval = clipped(lo, hi, domain_lo, domain_hi)
                        if interval:
                            type_ii_intervals.append(interval)

                if type_ii_intervals:
                    a3_type_ii_boxes += 1
                a3_type_ii_intervals += len(type_ii_intervals)
                for _, b3_hi in type_ii_intervals:
                    residual = alpha_lo - b1_hi - b2_hi - b3_hi
                    a3_omega_argument.include(residual, b3_hi)

                # The first threshold t=2.01 has the largest admissible
                # beta3 interval; it is present iff any lower-sieve branch is.
                residual = half - b1_hi - b2_hi
                if residual > 0 and domain_lo < 100 * residual // 301:
                    a3_lower_sieve_boxes += 1

        # Recursive tail grid.  These are the exact outward-rounded bounds
        # used by the three implementations.
        ab = alpha_bounds(i, alpha_steps)
        if not (0 < ab.gamma_min and ab.tau_max < ab.a_min):
            continue
        tail_width = ab.a_min - ab.tau_max
        for i1 in range(tail_steps):
            b1_lo = ab.tau_max + tail_width * i1 // tail_steps
            b1_hi = ab.tau_max + tail_width * (i1 + 1) // tail_steps
            if not (0 < b1_lo < b1_hi):
                continue
            tail_nodes += 1
            tail_base_argument.include(ab.alpha_lo - b1_hi, ab.gamma_max)

            child_width = b1_hi - ab.gamma_min
            for i2 in range(tail_steps):
                b2_lo = ab.gamma_min + child_width * i2 // tail_steps
                b2_hi = ab.gamma_min + child_width * (i2 + 1) // tail_steps
                tail_pair_boxes += 1
                if not (0 < b2_lo < b2_hi):
                    tail_invalid_pair_boxes += 1
                    continue
                selected_hi = b1_hi + b2_hi
                delta_min = SCALE // 2 - selected_hi
                if delta_min <= 0:
                    tail_invalid_pair_boxes += 1
                    continue

                tail_linear_sieve_boxes += 1
                pair_type_ii = (
                    ab.a_max <= b1_lo + b2_lo and
                    b1_hi + b2_hi <= ab.sigma_min
                )
                if pair_type_ii:
                    tail_type_ii_boxes += 1
                    pair_type_ii_argument.include(
                        ab.alpha_lo - selected_hi, b2_hi)
                    continue

                recursive = (
                    selected_hi <= ab.xi_min and
                    0 < ab.gamma_min and
                    ab.gamma_max < b2_lo
                )
                if recursive:
                    tail_recursive_boxes += 1
                    recursive_base_argument.include(
                        ab.alpha_lo - selected_hi, ab.gamma_max)
                else:
                    tail_linear_only_boxes += 1

    assert retained_alpha_cells == cutoff_index
    assert a3_type_ii_intervals > 0
    assert a3_lower_sieve_boxes > 0
    assert tail_type_ii_boxes > 0
    assert tail_recursive_boxes > 0
    assert tail_linear_only_boxes > 0

    # u_- is used only for Buchstab arguments at least 2.47; u_+ only for
    # arguments at least 4.  These checks are proof-adverse over whole cells.
    assert a3_omega_argument.at_least(247, 100)
    assert tail_base_argument.at_least(247, 100)
    assert pair_type_ii_argument.at_least(4, 1)
    assert recursive_base_argument.at_least(4, 1)

    print(f"retained_alpha_cells={retained_alpha_cells}")
    print(f"a3_ordered_boxes={a3_boxes}")
    print(f"a3_type_ii_boxes={a3_type_ii_boxes}")
    print(f"a3_type_ii_intervals={a3_type_ii_intervals}")
    print(f"a3_lower_sieve_boxes={a3_lower_sieve_boxes}")
    print(f"tail_nodes={tail_nodes}")
    print(f"tail_pair_boxes={tail_pair_boxes}")
    print(f"tail_invalid_pair_boxes={tail_invalid_pair_boxes}")
    print(f"tail_linear_sieve_boxes={tail_linear_sieve_boxes}")
    print(f"tail_type_ii_boxes={tail_type_ii_boxes}")
    print(f"tail_recursive_boxes={tail_recursive_boxes}")
    print(f"tail_linear_only_boxes={tail_linear_only_boxes}")
    print(f"min_a3_omega_argument={a3_omega_argument.decimal()}")
    print(f"min_tail_base_argument={tail_base_argument.decimal()}")
    print(f"min_pair_type_ii_argument={pair_type_ii_argument.decimal()}")
    print(f"min_recursive_base_argument={recursive_base_argument.decimal()}")
    print("BRANCH_LEDGER_CERTIFIED=YES")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

