#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

// Outward-rounded integer certificate for the recursive one-prime tail in
// the Harman F5 range.  This extends certify_harman_switching.cpp by:
//
//   * a rational lower-linear-sieve envelope in the A3 term; and
//   * a lower bound for the omitted tau < beta_1 < alpha-1 branch, obtained
//     from a Fundamental-Proposition base minus recursively improved child
//     upper bounds.
//
// Every stored real quantity is bounded by an integer multiple of 1e-12.
// Geometry endpoints are either exact rationals over a common denominator
// or inward/outward fixed-point endpoints.  No floating-point operation is
// used.

namespace {

using i64 = std::int64_t;
using i128 = __int128_t;

constexpr i64 kScale = 1'000'000'000'000LL;
constexpr i64 kOmegaUpper = 561'700'000'000LL;
constexpr i64 kOmegaLower = 560'700'000'000LL;
constexpr i64 kHalf = kScale / 2;
constexpr int kMaxGridSteps = 20'000;

i64 checked_i64(i128 value) {
  if (value < std::numeric_limits<i64>::min() ||
      value > std::numeric_limits<i64>::max()) {
    throw std::overflow_error("fixed-point integer overflow");
  }
  return static_cast<i64>(value);
}

i64 floor_ratio_scaled(i128 numerator, i128 denominator) {
  if (numerator < 0 || denominator <= 0) {
    throw std::domain_error("floor_ratio_scaled expects nonnegative input");
  }
  return checked_i64(static_cast<i128>(kScale) * numerator / denominator);
}

i64 ceil_ratio_scaled(i128 numerator, i128 denominator) {
  if (numerator < 0 || denominator <= 0) {
    throw std::domain_error("ceil_ratio_scaled expects nonnegative input");
  }
  const i128 value = static_cast<i128>(kScale) * numerator;
  return checked_i64((value + denominator - 1) / denominator);
}

i64 floor_ratio(i128 numerator, i128 denominator) {
  if (numerator < 0 || denominator <= 0) {
    throw std::domain_error("floor_ratio expects nonnegative input");
  }
  return checked_i64(numerator / denominator);
}

i64 mul_down(i64 x, i64 y) {
  if (x < 0 || y < 0) throw std::domain_error("mul_down negative input");
  return checked_i64(static_cast<i128>(x) * y / kScale);
}

i64 mul_up(i64 x, i64 y) {
  if (x < 0 || y < 0) throw std::domain_error("mul_up negative input");
  const i128 value = static_cast<i128>(x) * y;
  return checked_i64((value + kScale - 1) / kScale);
}

i64 reciprocal_lower(i64 denominator, i64 numerator) {
  return floor_ratio_scaled(denominator, numerator);
}

i64 reciprocal_upper(i64 denominator, i64 numerator) {
  return ceil_ratio_scaled(denominator, numerator);
}

struct WeightedInterval {
  i64 lo;
  i64 hi;
  i64 weight_lower;
};

void add_weighted_interval(std::vector<WeightedInterval>& intervals,
                           i64 lo, i64 hi, i64 weight_lower,
                           i64 domain_lo, i64 domain_hi) {
  lo = std::max(lo, domain_lo);
  hi = std::min(hi, domain_hi);
  if (lo < hi && weight_lower > 0) {
    intervals.push_back({lo, hi, weight_lower});
  }
}

// Lower bound for integral max_j(weight_j 1_Ij) db/b^2.  All interval
// endpoints are integer numerators over the same positive denominator.
i64 weighted_reciprocal_integral_lower(
    const std::vector<WeightedInterval>& intervals, i64 denominator) {
  if (intervals.empty()) return 0;
  std::vector<i64> endpoints;
  endpoints.reserve(2 * intervals.size());
  for (const auto& interval : intervals) {
    endpoints.push_back(interval.lo);
    endpoints.push_back(interval.hi);
  }
  std::sort(endpoints.begin(), endpoints.end());
  endpoints.erase(std::unique(endpoints.begin(), endpoints.end()),
                  endpoints.end());

  i64 answer = 0;
  for (std::size_t j = 1; j < endpoints.size(); ++j) {
    const i64 lo = endpoints[j - 1];
    const i64 hi = endpoints[j];
    if (!(0 < lo && lo < hi)) continue;
    i64 weight = 0;
    for (const auto& interval : intervals) {
      if (interval.lo <= lo && hi <= interval.hi) {
        weight = std::max(weight, interval.weight_lower);
      }
    }
    if (weight == 0) continue;
    const i64 left = reciprocal_lower(denominator, lo);
    const i64 right = reciprocal_upper(denominator, hi);
    if (left > right) {
      answer = checked_i64(static_cast<i128>(answer) +
                           mul_down(left - right, weight));
    }
  }
  return answer;
}

struct Threshold {
  i64 p;
  i64 q;
  i64 weight_lower;
};

// For t=p/q in [2,4], weight=4(t-2)/t^2.  The final t=4 entry also
// licenses the constant 1/2 continuation for larger sieve parameter.
const std::vector<Threshold>& lower_sieve_thresholds() {
  static const std::vector<Threshold> values = [] {
    const std::pair<i64, i64> raw[] = {
        {201, 100}, {21, 10}, {11, 5}, {23, 10}, {12, 5}, {5, 2},
        {13, 5}, {27, 10}, {14, 5}, {29, 10}, {3, 1}, {31, 10},
        {16, 5}, {33, 10}, {17, 5}, {7, 2}, {18, 5}, {37, 10},
        {19, 5}, {39, 10}, {4, 1}};
    std::vector<Threshold> result;
    for (const auto& [p, q] : raw) {
      const i128 numerator = static_cast<i128>(4) * (p - 2 * q) * q;
      const i128 denominator = static_cast<i128>(p) * p;
      result.push_back({p, q,
                        floor_ratio_scaled(numerator, denominator)});
    }
    return result;
  }();
  return values;
}

// Add all uniform Type-II and rational lower-sieve intervals for a third
// ordered prime.  Exponent endpoints share `denominator`.
void add_third_prime_lower_intervals(
    std::vector<WeightedInterval>& intervals,
    i64 b1_lo, i64 b1_hi, i64 b2_lo, i64 b2_hi,
    i64 domain_lo, i64 domain_hi, i64 a_max, i64 sigma_min,
    i64 half) {
  if (!(domain_lo < domain_hi)) return;

  const bool pair12_good =
      a_max <= b1_lo + b2_lo && b1_hi + b2_hi <= sigma_min;
  if (pair12_good) {
    add_weighted_interval(intervals, domain_lo, domain_hi, kOmegaLower,
                          domain_lo, domain_hi);
  } else {
    add_weighted_interval(intervals, a_max - b1_lo,
                          sigma_min - b1_hi, kOmegaLower,
                          domain_lo, domain_hi);
    add_weighted_interval(intervals, a_max - b2_lo,
                          sigma_min - b2_hi, kOmegaLower,
                          domain_lo, domain_hi);
    add_weighted_interval(intervals, a_max - b1_lo - b2_lo,
                          sigma_min - b1_hi - b2_hi, kOmegaLower,
                          domain_lo, domain_hi);
  }

  const i64 residual = half - b1_hi - b2_hi;
  if (residual <= 0) return;
  for (const auto& threshold : lower_sieve_thresholds()) {
    // b3 <= residual/(t+1) = q*residual/(p+q).
    const i64 upper = floor_ratio(
        static_cast<i128>(threshold.q) * residual,
        threshold.p + threshold.q);
    add_weighted_interval(intervals, domain_lo, upper,
                          threshold.weight_lower, domain_lo, domain_hi);
  }
}

struct AlphaBounds {
  i64 alpha_lo;
  i64 alpha_hi;
  i64 gamma_min;
  i64 gamma_max;
  i64 tau_max;
  i64 a_min;
  i64 a_max;
  i64 sigma_min;
  i64 xi_min;
};

AlphaBounds alpha_bounds(int index, int steps) {
  const i64 n = steps;
  const i64 lo_num = 14 * n + index;
  const i64 hi_num = lo_num + 1;
  AlphaBounds out;
  out.alpha_lo = floor_ratio_scaled(lo_num, 12 * static_cast<i128>(n));
  out.alpha_hi = ceil_ratio_scaled(hi_num, 12 * static_cast<i128>(n));
  out.gamma_min = floor_ratio_scaled(
      60 * static_cast<i128>(n) - 4 * static_cast<i128>(hi_num),
      36 * static_cast<i128>(n));
  out.gamma_max = ceil_ratio_scaled(
      60 * static_cast<i128>(n) - 4 * static_cast<i128>(lo_num),
      36 * static_cast<i128>(n));
  out.tau_max = ceil_ratio_scaled(
      18 * static_cast<i128>(n) - lo_num, 24 * static_cast<i128>(n));
  out.a_min = floor_ratio_scaled(lo_num - 12 * static_cast<i128>(n),
                                 12 * static_cast<i128>(n));
  out.a_max = ceil_ratio_scaled(hi_num - 12 * static_cast<i128>(n),
                                12 * static_cast<i128>(n));
  out.sigma_min = floor_ratio_scaled(
      24 * static_cast<i128>(n) - hi_num, 36 * static_cast<i128>(n));
  out.xi_min = floor_ratio_scaled(
      18 * static_cast<i128>(n) - hi_num, 12 * static_cast<i128>(n));
  return out;
}

struct Cell {
  i64 lo;
  i64 hi;
};

Cell equal_cell(i64 lo, i64 hi, int index, int steps) {
  const i64 width = hi - lo;
  return {
      checked_i64(static_cast<i128>(lo) +
                  static_cast<i128>(width) * index / steps),
      checked_i64(static_cast<i128>(lo) +
                  static_cast<i128>(width) * (index + 1) / steps),
  };
}

i64 pair_child_upper(const AlphaBounds& ab, const Cell& b1,
                     const Cell& b2) {
  if (!(0 < b2.lo && b2.lo < b2.hi)) return std::numeric_limits<i64>::max();
  const i64 selected_hi = b1.hi + b2.hi;
  const i64 delta_min = kHalf - selected_hi;
  if (delta_min <= 0) return std::numeric_limits<i64>::max();

  // Universal proof-adverse upper envelope for the two branches of F(s).
  const i64 by_delta = ceil_ratio_scaled(2 * static_cast<i128>(kScale),
                                         delta_min);
  const i64 by_beta = ceil_ratio_scaled(2 * static_cast<i128>(kScale),
                                        3 * static_cast<i128>(b2.lo));
  i64 best = std::max(by_delta, by_beta);

  const bool pair_type_ii =
      ab.a_max <= b1.lo + b2.lo && b1.hi + b2.hi <= ab.sigma_min;
  if (pair_type_ii) {
    best = std::min(best, ceil_ratio_scaled(kOmegaUpper, b2.lo));
    return best;
  }

  if (selected_hi <= ab.xi_min && ab.gamma_min > 0) {
    const i64 base_upper =
        ceil_ratio_scaled(kOmegaUpper, ab.gamma_min);
    const i64 domain_lo = ab.gamma_max;
    const i64 domain_hi = b2.lo;
    if (domain_lo < domain_hi) {
      std::vector<WeightedInterval> intervals;
      intervals.reserve(4 + lower_sieve_thresholds().size());
      add_third_prime_lower_intervals(
          intervals, b1.lo, b1.hi, b2.lo, b2.hi,
          domain_lo, domain_hi, ab.a_max, ab.sigma_min, kHalf);
      const i64 children_lower =
          weighted_reciprocal_integral_lower(intervals, kScale);
      if (children_lower <= base_upper) {
        best = std::min(best, base_upper - children_lower);
      }
    }
  }
  return best;
}

// Lower bound for the omitted tau<beta_1<a tail on one alpha cell.
i64 tail_lower(const AlphaBounds& ab, int beta_steps) {
  if (!(0 < ab.gamma_min && ab.tau_max < ab.a_min)) return 0;
  i64 answer = 0;
  for (int i1 = 0; i1 < beta_steps; ++i1) {
    const Cell b1 = equal_cell(ab.tau_max, ab.a_min, i1, beta_steps);
    if (!(0 < b1.lo && b1.lo < b1.hi)) continue;
    const i64 base_lower =
        floor_ratio_scaled(kOmegaLower, ab.gamma_max);

    i64 children_upper = 0;
    // A containing q2 domain.  The same-cell region is deliberately
    // included in full, so distinct primes in one exponent box are not lost.
    for (int i2 = 0; i2 < beta_steps; ++i2) {
      const Cell b2 = equal_cell(ab.gamma_min, b1.hi, i2, beta_steps);
      if (!(0 < b2.lo && b2.lo < b2.hi)) continue;
      const i64 upper = pair_child_upper(ab, b1, b2);
      if (upper == std::numeric_limits<i64>::max()) {
        children_upper = std::numeric_limits<i64>::max();
        break;
      }
      const i64 log_weight_upper =
          ceil_ratio_scaled(b2.hi - b2.lo, b2.lo);
      children_upper = checked_i64(
          static_cast<i128>(children_upper) +
          mul_up(upper, log_weight_upper));
    }
    if (children_upper == std::numeric_limits<i64>::max() ||
        base_lower <= children_upper) {
      continue;
    }
    const i64 node_lower = base_lower - children_upper;
    const i64 log_weight_lower =
        floor_ratio_scaled(b1.hi - b1.lo, b1.hi);
    i64 contribution = mul_down(ab.alpha_lo, node_lower);
    contribution = mul_down(contribution, log_weight_lower);
    answer = checked_i64(static_cast<i128>(answer) + contribution);
  }
  return answer;
}

struct CellBounds {
  i64 saving_lower;
  i64 tail_lower;
  i64 a3_lower;
};

CellBounds certify_cell(int alpha_index, int alpha_steps, int beta_steps,
                        int tail_beta_steps) {
  const i64 n = alpha_steps;
  const i64 b = beta_steps;
  const i64 i = alpha_index;
  const i64 alpha_lo_num = 14 * n + i;
  const i64 alpha_hi_num = alpha_lo_num + 1;

  // Retain only alpha<1.22.  Zero elsewhere is a valid lower bound.
  if (100 * alpha_lo_num >= 122 * 12 * n || i == n - 1) {
    return {0, 0, 0};
  }

  const i64 den = 72 * n * b;
  const i64 common_width_num = 4 * n + 5 * i - 3;
  const i64 containing_width_num = 4 * n + 5 * i + 8;
  if (common_width_num <= 0) return {0, 0, 0};
  auto common_beta_num = [&](i64 k) {
    return 8 * b * (n - i) + k * common_width_num;
  };
  auto containing_beta_num = [&](i64 k) {
    return 8 * b * (n - i - 1) + k * containing_width_num;
  };

  const i64 alpha_over_gamma_upper = ceil_ratio_scaled(
      3 * static_cast<i128>(alpha_hi_num),
      4 * static_cast<i128>(n - i - 1));
  const i64 a0_upper = mul_up(kOmegaUpper, alpha_over_gamma_upper);

  i64 common_log_lower = 0;
  for (i64 k = 1; k <= b; ++k) {
    common_log_lower = checked_i64(
        static_cast<i128>(common_log_lower) +
        floor_ratio_scaled(common_width_num, common_beta_num(k)));
  }
  const i64 alpha_over_gamma_lower = floor_ratio_scaled(
      3 * static_cast<i128>(alpha_lo_num),
      4 * static_cast<i128>(n - i));
  i64 a1_lower = mul_down(kOmegaLower, alpha_over_gamma_lower);
  a1_lower = mul_down(a1_lower, common_log_lower);

  i64 containing_log_upper = 0;
  for (i64 k = 0; k < b; ++k) {
    containing_log_upper = checked_i64(
        static_cast<i128>(containing_log_upper) +
        ceil_ratio_scaled(containing_width_num, containing_beta_num(k)));
  }
  const i64 log_square_upper =
      mul_up(containing_log_upper, containing_log_upper);
  i64 a2_upper = mul_up(kOmegaUpper, alpha_over_gamma_upper);
  a2_upper = mul_up(a2_upper, log_square_upper);
  a2_upper = (a2_upper + 1) / 2;

  const i64 type_ii_lo_num = (2 * n + i + 1) * 6 * b;
  const i64 type_ii_hi_num = (10 * n - i - 1) * 2 * b;
  const i64 gamma_num = common_beta_num(0);
  const i64 half_num = den / 2;
  const i64 alpha_lo_lower = floor_ratio_scaled(
      alpha_lo_num, 12 * static_cast<i128>(n));
  const i64 common_width_lower =
      floor_ratio_scaled(common_width_num, den);
  const i64 width_square_lower =
      mul_down(common_width_lower, common_width_lower);
  i64 weighted_triple_lower = 0;

  for (i64 i1 = 1; i1 < b; ++i1) {
    const i64 b1_lo = common_beta_num(i1);
    const i64 b1_hi = common_beta_num(i1 + 1);
    i64 row_lower = 0;
    for (i64 i2 = 1; i2 < i1; ++i2) {
      const i64 b2_lo = common_beta_num(i2);
      const i64 b2_hi = common_beta_num(i2 + 1);
      std::vector<WeightedInterval> intervals;
      intervals.reserve(4 + lower_sieve_thresholds().size());
      add_third_prime_lower_intervals(
          intervals, b1_lo, b1_hi, b2_lo, b2_hi,
          gamma_num, b2_lo, type_ii_lo_num, type_ii_hi_num, half_num);
      const i64 beta3_lower =
          weighted_reciprocal_integral_lower(intervals, den);
      const i64 reciprocal_b1b2_lower = floor_ratio_scaled(
          static_cast<i128>(den) * den,
          static_cast<i128>(b1_hi) * b2_hi);
      row_lower = checked_i64(
          static_cast<i128>(row_lower) +
          mul_down(beta3_lower, reciprocal_b1b2_lower));
    }
    weighted_triple_lower = checked_i64(
        static_cast<i128>(weighted_triple_lower) +
        mul_down(width_square_lower, row_lower));
  }
  const i64 a3_lower =
      mul_down(alpha_lo_lower, weighted_triple_lower);

  const AlphaBounds ab = alpha_bounds(alpha_index, alpha_steps);
  const i64 retained_tail_lower = tail_lower(ab, tail_beta_steps);

  const i64 linear_lower = floor_ratio_scaled(
      4 * static_cast<i128>(alpha_lo_num),
      12 * static_cast<i128>(n));
  const i64 switched_upper = checked_i64(
      static_cast<i128>(a0_upper) - a1_lower + a2_upper - a3_lower -
      retained_tail_lower);
  const i64 saving_lower =
      std::max<i64>(0, linear_lower - switched_upper);
  return {saving_lower, retained_tail_lower, a3_lower};
}

void print_decimal(i64 scaled) {
  std::cout << scaled / kScale << '.' << std::setw(12)
            << std::setfill('0') << scaled % kScale << std::setfill(' ');
}

}  // namespace

int main(int argc, char** argv) {
  const int alpha_steps = argc > 1 ? std::stoi(argv[1]) : 600;
  const int beta_steps = argc > 2 ? std::stoi(argv[2]) : 160;
  const int tail_beta_steps = argc > 3 ? std::stoi(argv[3]) : 80;
  const bool dump_cells = argc > 4 && std::string(argv[4]) == "--dump-cells";
  if (argc > 5 || (argc > 4 && !dump_cells) ||
      alpha_steps <= 1 || beta_steps <= 4 ||
      tail_beta_steps <= 4 || alpha_steps > kMaxGridSteps ||
      beta_steps > kMaxGridSteps || tail_beta_steps > kMaxGridSteps) {
    std::cerr << "usage: certify_harman_recursive_tail "
                 "[alpha_steps beta_steps tail_beta_steps [--dump-cells]]\n";
    return 2;
  }

  i128 sum = 0;
  i128 tail_sum = 0;
  i128 a3_sum = 0;
  int positive = 0;
  for (int i = 0; i < alpha_steps; ++i) {
    const CellBounds value =
        certify_cell(i, alpha_steps, beta_steps, tail_beta_steps);
    if (dump_cells) {
      std::cout << "cell=" << i
                << ",saving=" << value.saving_lower
                << ",tail=" << value.tail_lower
                << ",a3=" << value.a3_lower << '\n';
    }
    sum += value.saving_lower;
    tail_sum += value.tail_lower;
    a3_sum += value.a3_lower;
    if (value.saving_lower > 0) ++positive;
  }
  const i64 denominator = 12LL * alpha_steps;
  const i64 saving = checked_i64(sum / denominator);
  const i64 tail_integral = checked_i64(tail_sum / denominator);
  const i64 a3_integral = checked_i64(a3_sum / denominator);
  const i64 target = 32'000'000'000LL;

  std::cout << "scale=" << kScale << '\n';
  std::cout << "alpha_steps=" << alpha_steps
            << " beta_steps=" << beta_steps
            << " tail_beta_steps=" << tail_beta_steps << '\n';
  std::cout << "positive_alpha_cells=" << positive << '\n';
  std::cout << "tail_lower_integral=";
  print_decimal(tail_integral);
  std::cout << '\n';
  std::cout << "a3_lower_integral=";
  print_decimal(a3_integral);
  std::cout << '\n';
  std::cout << "saving_lower_units=" << saving << '\n';
  std::cout << "saving_lower=";
  print_decimal(saving);
  std::cout << '\n';
  std::cout << "target=";
  print_decimal(target);
  std::cout << '\n';
  std::cout << "CERTIFIED=" << (saving > target ? "YES" : "NO") << '\n';
  return saving > target ? 0 : 1;
}
