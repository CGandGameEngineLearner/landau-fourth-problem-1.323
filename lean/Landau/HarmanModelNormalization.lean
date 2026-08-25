import Landau.HarmanProofAdverseGeometry
import Landau.LinearSieveRationalEnvelope

namespace Landau

/-!
# Gate 5: algebraic model normalization

The theorems below match the rational constants and changes of variables in
the paper to the integer formulas used by the certificate.  They address
publication-review gate 5 only.  They do **not** prove Merikoski's Lemma 7,
the analytic origin of the dimension-one sieve functions, or the passage
from a sifted sum to a model integral.
-/

/-- Gate 5 (`A₀/A₁/A₂` normalization): the paper's factor `α/γ(α)` is
algebraically `3α/(5-4α)`.  This identity does not supply the Buchstab or
Fundamental-Proposition estimate multiplying that factor. -/
theorem alpha_div_gamma_eq_three_alpha_div
    (alpha : ℚ) :
    alpha / switchingGammaQ alpha = 3 * alpha / (5 - 4 * alpha) := by
  unfold switchingGammaQ
  by_cases h : 5 - 4 * alpha = 0
  · simp [h]
  · field_simp
    ring

/-- Gate 5 (certificate/code alignment): on an alpha cell, the exact
`α_hi/γ(α_hi)` ratio equals the rational expression whose outward-rounded
integer implementation is `ceilScaled (3*hiNum) (4*(n-i-1))`.  This is an
endpoint identity, not the analytic `A₀` upper bound. -/
theorem alpha_hi_div_gamma_eq_certificate_ratio
    {n i : Nat} (hn : 0 < n) (hi : i + 1 < n) :
    alphaCellHiQ n i / switchingGammaQ (alphaCellHiQ n i) =
      ((3 * (14 * n + i + 1) : Nat) : ℚ) /
        (4 * (n - i - 1) : Nat) := by
  have hsub : i + 1 ≤ n := Nat.le_of_lt hi
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgap : (n : ℚ) - i - 1 ≠ 0 := by
    have hcast : (i : ℚ) + 1 < n := by exact_mod_cast hi
    linarith
  have hden : 5 - 4 * alphaCellHiQ n i =
      4 * ((n : ℚ) - i - 1) / (12 * (n : ℚ)) := by
    unfold alphaCellHiQ
    push_cast
    field_simp [hnq]
    ring
  calc
    alphaCellHiQ n i / switchingGammaQ (alphaCellHiQ n i) =
        3 * alphaCellHiQ n i / (5 - 4 * alphaCellHiQ n i) :=
      alpha_div_gamma_eq_three_alpha_div _
    _ = 3 * (((14 * n + i + 1 : Nat) : ℚ) / (12 * n : Nat)) /
        (4 * ((n : ℚ) - i - 1) / (12 * (n : ℚ))) := by
      rw [hden]
      rfl
    _ = ((3 * (14 * n + i + 1) : Nat) : ℚ) /
        (4 * (n - i - 1) : Nat) := by
      have hsubeq : n - i - 1 = n - (i + 1) := by omega
      have hdenCast : (((4 * (n - i - 1) : Nat) : ℚ)) =
          4 * ((n : ℚ) - i - 1) := by
        rw [hsubeq]
        push_cast [Nat.cast_sub hsub]
        ring
      have hnumCast : (((3 * (14 * n + i + 1) : Nat) : ℚ)) =
          3 * ((14 * n + i + 1 : Nat) : ℚ) := by
        push_cast
        ring
      rw [hdenCast, hnumCast]
      field_simp [hnq, hgap]

/-- Gate 5 (`t+1` threshold): with `s₃=residual/β₃-1`, the lower-sieve
condition `s₃≥p/q` is exactly the upper endpoint
`β₃≤q*residual/(p+q)`.  This proves the algebra behind the code's `t+1`;
it does not prove that a linear-sieve weight is available there. -/
theorem sieve_parameter_ge_iff_beta_le_threshold
    {residual beta p q : ℚ}
    (hbeta : 0 < beta) (hq : 0 < q) (hpq : 0 < p + q) :
    p / q ≤ residual / beta - 1 ↔
      beta ≤ q * residual / (p + q) := by
  constructor
  · intro h
    have h1 : p ≤ (residual / beta - 1) * q :=
      (div_le_iff₀ hq).mp h
    rw [div_sub_one hbeta.ne', div_mul_eq_mul_div] at h1
    have h2 : p * beta ≤ (residual - beta) * q :=
      (le_div_iff₀ hbeta).mp h1
    apply (le_div_iff₀ hpq).2
    nlinarith
  · intro h
    have h' := (le_div_iff₀ hpq).mp h
    apply (div_le_iff₀ hq).2
    rw [div_sub_one hbeta.ne', div_mul_eq_mul_div]
    apply (le_div_iff₀ hbeta).2
    nlinarith

/-- Gate 5 (`t+1` code formula): the integer numerator
`q*residual/(p+q)` has the stated rational prototype.  This is a cast
identity only and does not certify the associated sieve weight. -/
theorem threshold_upper_rational_prototype
    (p q residual : Nat) :
    (((q * residual : Nat) : ℚ) / (p + q : Nat)) =
      (q : ℚ) * residual / (p + q) := by
  norm_num

/-- Gate 5 (`Φ` normalization): for `t=p/q`, the rational envelope
`4(t-2)/t²` equals `4(p-2q)q/p²`.  This is the formula sampled by
`sieveThresholds`; it does not prove that `Φ≤e^{-γ}f`. -/
theorem rational_phi_at_fraction
    {p q : ℚ} (hp : p ≠ 0) (hq : q ≠ 0) :
    4 * (p / q - 2) / (p / q) ^ 2 =
      4 * (p - 2 * q) * q / p ^ 2 := by
  field_simp
  ring

/-- Gate 5 (`Φ` code alignment): under `2q≤p`, the natural-number formula
used before `floorScaled` casts to the paper's rational
`4(p-2q)q/p²`.  It does not reprove the analytic lower-sieve envelope. -/
theorem sieveThreshold_weight_rational_prototype
    {p q : Nat} (h2 : 2 * q ≤ p) :
    (((4 * (p - 2 * q) * q : Nat) : ℚ) / (p * p : Nat)) =
      4 * ((p : ℚ) - 2 * q) * q / (p : ℚ) ^ 2 := by
  push_cast [Nat.cast_sub h2]
  norm_num [pow_two]

/-- Gate 5 (`Φ` outward rounding): `floorScaled` is below the exact rational
weight sampled by `sieveThresholds`.  This is only a fixed-point rounding
fact; the standard linear-sieve theorem remains external. -/
theorem sieveThreshold_floorScaled_le_phi
    {p q : Nat} (hp : 0 < p) (h2 : 2 * q ≤ p) :
    ((floorScaled (4 * (p - 2 * q) * q) (p * p) : Nat) : ℚ) / scale ≤
      4 * ((p : ℚ) - 2 * q) * q / (p : ℚ) ^ 2 := by
  rw [← sieveThreshold_weight_rational_prototype h2]
  exact floorScaled_spec _ _ (Nat.mul_pos hp hp)

/-- Gate 5 (`U_LS` normalization): if `s=δ₂/β₂`, then the normalized
upper-sieve factor `(2/s)` multiplied by `dβ₂/β₂` has coefficient `2/δ₂`.
This is algebra for the `1/β²` measure convention, not a proof of the
formula for the standard upper-sieve function `F`. -/
theorem upper_sieve_measure_coefficient
    {delta beta : ℚ} (hdelta : delta ≠ 0) (hbeta : beta ≠ 0) :
    (2 / (delta / beta)) / beta = 2 / delta := by
  field_simp
  ring

def upperLinearSieveEnvelopeQ (beta1 beta2 : ℚ) : ℚ :=
  max (2 / (1 / 2 - beta1 - beta2)) (2 / (3 * beta2))

/-- Gate 5 (`U_LS` definition): the rational envelope recorded by the code
is exactly `max(2/δ₂,2/(3β₂))` with `δ₂=1/2-β₁-β₂`.  This definitional
identity does not establish that either branch bounds a real sifted sum. -/
theorem upperLinearSieveEnvelopeQ_eq (beta1 beta2 : ℚ) :
    upperLinearSieveEnvelopeQ beta1 beta2 =
      max (2 / (1 / 2 - beta1 - beta2)) (2 / (3 * beta2)) := by
  rfl

/-- Gate 5 (`U_LS` integer alignment): the `byDelta` expression in
`pairChildUpper` is an outward-rounded upper bound for
`2/(delta/scale)`.  This proves rounding only, not the linear sieve. -/
theorem pair_byDelta_rounds_up {delta : Nat} (hdelta : 0 < delta) :
    (2 : ℚ) / ((delta : ℚ) / scale) ≤
      ((ceilScaled (2 * scale) delta : Nat) : ℚ) / scale := by
  convert ceilScaled_spec (2 * scale) delta hdelta using 1
  field_simp

/-- Gate 5 (`U_LS` integer alignment): the `byBeta` expression in
`pairChildUpper` is an outward-rounded upper bound for `2/(3β₂)` when
`β₂=b/scale`.  This is a rounding statement only. -/
theorem pair_byBeta_rounds_up {b : Nat} (hb : 0 < b) :
    (2 : ℚ) / (3 * ((b : ℚ) / scale)) ≤
      ((ceilScaled (2 * scale) (3 * b) : Nat) : ℚ) / scale := by
  have h3b : 0 < 3 * b := Nat.mul_pos (by norm_num) hb
  convert ceilScaled_spec (2 * scale) (3 * b) h3b using 1
  field_simp

end Landau
