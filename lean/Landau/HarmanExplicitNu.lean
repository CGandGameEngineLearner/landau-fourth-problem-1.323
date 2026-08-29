import Landau.HarmanTypeIIInterior
import Landau.HarmanRecursiveEndpoint

namespace Landau

/-!
# Explicit finite `ν` and margin split

The paper fixes one positive rational `ν` before taking `x→∞`.  This module
checks that it satisfies every affine constraint on
`7/6<α<1.22` and the final arithmetic implied by the paper's analytic bound
`|Δ_ν-Δ| ≤ 10^11 ν`.  It does **not** prove that analytic integral bound.
-/

/-- A fixed interior margin small enough for every affine constraint and
the paper's explicit analytic-loss budget on `α<1.22`. -/
def explicitNu : ℚ := 1 / 10 ^ 20

theorem explicitNu_pos : 0 < explicitNu := by
  norm_num [explicitNu]

/-- `4ν < 1/25 < γ(α)` throughout `α<1.22`. -/
theorem explicitNu_lt_gamma_lower : 4 * explicitNu < 1 / 25 := by
  norm_num [explicitNu]

/-- `5ν < 1/25 ≤ σ-a = γ` throughout `α<1.22`, so `[a_ν,σ_ν]` stays
strictly inside the Type-II interval. -/
theorem explicitNu_lt_typeII_gap : 5 * explicitNu < 1 / 25 := by
  norm_num [explicitNu]

theorem explicitNu_fits_gamma
    {alpha : ℚ} (halpha : alpha < 122 / 100) :
    4 * explicitNu < interiorGamma alpha :=
  lt_trans explicitNu_lt_gamma_lower (gamma_gt_one_twenty_fifth halpha)

theorem explicitNu_fits_typeII_gap
    {alpha : ℚ} (halpha : alpha < 122 / 100) :
    5 * explicitNu < interiorSigma alpha - interiorA alpha := by
  rw [interior_sigma_sub_a]
  exact lt_trans explicitNu_lt_typeII_gap (gamma_gt_one_twenty_fifth halpha)

/-- Gate 1 (explicit `ν`): on the retained range the fixed rational value
puts `[a_ν,σ_ν]` strictly inside the published Type-II interval.  This is
finite margin algebra, not Corollary 7.2. -/
theorem explicit_nu_typeII_interior
    {alpha : ℚ} (halpha : alpha < 122 / 100) :
    interiorA alpha + 2 * explicitNu < interiorANu alpha explicitNu ∧
    interiorANu alpha explicitNu < interiorSigmaNu alpha explicitNu ∧
    interiorSigmaNu alpha explicitNu <
      interiorSigma alpha - 4 * explicitNu / 3 :=
  interior_typeII_interval_strict explicitNu_pos
    (explicitNu_fits_typeII_gap halpha)

/-- Gate 1 (explicit `ν`): on `7/6<α<1.22` the same value keeps
`0<γ_ν<τ_ν<a<σ`. -/
theorem explicit_nu_shifted_order
    {alpha : ℚ} (hlo : 7 / 6 < alpha) (hhi : alpha < 122 / 100) :
    0 < interiorGammaNu alpha explicitNu ∧
    interiorGammaNu alpha explicitNu < interiorTauNu alpha explicitNu ∧
    interiorTauNu alpha explicitNu < interiorA alpha ∧
    interiorA alpha < interiorSigma alpha :=
  interior_shifted_parameter_order hlo hhi explicitNu_pos
    (explicitNu_fits_gamma hhi)

/-- Gate 3 (explicit `ν` at `α=7/6`): the three-prime remainder height stays
at least `7/20000`. -/
theorem explicit_nu_three_prime_level
    {s0 : ℚ} (hs0 : s0 ≤ 3 * interiorTauNu (7 / 6) explicitNu) :
    (7 / 2 : ℚ) * explicitNu ≤ 1 / 2 - s0 - explicitNu :=
  three_prime_remainder_level_at_seven_six hs0

/-- Gate 3 (explicit `δ₀`): the fixed `ν` still gives a positive Type-I
power-saving exponent. -/
theorem explicit_nu_delta0 :
    (1 - 2 * selbergTheta) * explicitNu - explicitNu / 4 =
      17 / (32 * 10 ^ 20) ∧
    0 < (1 - 2 * selbergTheta) * explicitNu - explicitNu / 4 := by
  constructor
  · rw [prefix_remainder_delta0, explicitNu]
    norm_num
  · exact prefix_remainder_delta0_pos explicitNu_pos

/-- Gate 6 (half-margin comparison): the explicit algebraic `ν` is far
smaller than the displayed half margin, as rationals.  This is not a bound
on the integral `|H_ν-H|`. -/
theorem explicitNu_lt_half_margin :
    explicitNu < recursiveSwitchingHalfMargin := by
  norm_num [explicitNu, recursiveSwitchingHalfMargin]

/-- Gate 6 finite arithmetic: once the paper proves the analytic estimate
`|Δ_ν-Δ| ≤ 10^11 ν`, its chosen `ν` spends less than half the endpoint
margin.  This theorem checks only the last rational comparison. -/
theorem explicit_analytic_loss_lt_half_margin :
    (10 : ℚ) ^ 11 * explicitNu < recursiveSwitchingHalfMargin := by
  norm_num [explicitNu, recursiveSwitchingHalfMargin]

end Landau
