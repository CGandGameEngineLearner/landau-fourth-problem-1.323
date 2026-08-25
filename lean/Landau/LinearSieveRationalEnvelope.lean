import Mathlib

namespace Landau

/-!
# Rational envelope for the lower linear-sieve function

On `2 ≤ s ≤ 4`, the normalized dimension-one lower sieve function is

`e⁻ᵞ f(s) = 2 * log (s-1) / s`.

The lemmas below replace this transcendental expression by the rational
lower envelope `4(s-2)/s²`.  This is the envelope used by the recursive
Harman certificate search.
-/

/-- Rational function used as a lower envelope for the normalized lower
linear-sieve function on `[2,4]`. -/
noncomputable def rationalLowerSieveEnvelope (s : ℝ) : ℝ :=
  4 * (s - 2) / s ^ 2

/-- The elementary logarithm inequality needed to remove all transcendental
arithmetic from the lower-sieve certificate. -/
theorem rationalLowerSieveEnvelope_le_logFormula {s : ℝ} (hs : 2 ≤ s) :
    rationalLowerSieveEnvelope s ≤ 2 * Real.log (s - 1) / s := by
  have hspos : 0 < s := by linarith
  have hx : 0 ≤ s - 2 := by linarith
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hlog' : 2 * (s - 2) / s ≤ Real.log (s - 1) := by
    convert hlog using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hlog'
    (show 0 ≤ 2 / s by positivity)
  unfold rationalLowerSieveEnvelope
  convert hmul using 1 <;> field_simp <;> ring

/-- The rational envelope is increasing on `[2,4]`.  Hence an interval
certificate may evaluate it only at a lower bound for the sieve parameter. -/
theorem rationalLowerSieveEnvelope_monoOn {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 4) :
    rationalLowerSieveEnvelope s ≤ rationalLowerSieveEnvelope t := by
  have hspos : 0 < s := by linarith
  have htpos : 0 < t := by linarith
  have hfactor : 0 ≤ 2 * (s + t) - s * t := by
    have h1 : 0 ≤ (t - s) * (t - 2) :=
      mul_nonneg (sub_nonneg.mpr hst) (by linarith)
    have h2 : 0 ≤ t * (4 - t) :=
      mul_nonneg htpos.le (by linarith)
    nlinarith
  unfold rationalLowerSieveEnvelope
  apply (div_le_div_iff₀ (sq_pos_of_pos hspos) (sq_pos_of_pos htpos)).2
  have hprod : 0 ≤ (t - s) * (2 * (s + t) - s * t) :=
    mul_nonneg (sub_nonneg.mpr hst) hfactor
  nlinarith

/-- At the endpoint `s=4`, the rational envelope is exactly `1/2`. -/
theorem rationalLowerSieveEnvelope_four :
    rationalLowerSieveEnvelope 4 = 1 / 2 := by
  norm_num [rationalLowerSieveEnvelope]

/-- In particular, the exact normalized formula at `s=4` exceeds `1/2`.
Together with the standard monotonicity of the lower sieve function after
`4`, this licenses the constant continuation used by the certificate. -/
theorem half_le_lowerSieveLogFormula_at_four :
    (1 / 2 : ℝ) ≤ 2 * Real.log (4 - 1) / 4 := by
  rw [← rationalLowerSieveEnvelope_four]
  exact rationalLowerSieveEnvelope_le_logFormula (s := 4) (by norm_num)

end Landau
