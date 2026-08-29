import Mathlib

namespace Landau

/-!
# Gate 1: algebra of the Type-II interior margins

This module checks the affine identities and inequalities attached to the
paper's fixed `ν`-margins.  It does **not** prove Grimmelt--Merikoski
Corollary 7.1 or 7.2, their uniformity, or their applicability to any sifted
sum.
-/

def interiorA (alpha : ℚ) : ℚ := alpha - 1
def interiorSigma (alpha : ℚ) : ℚ := (2 - alpha) / 3
def interiorGamma (alpha : ℚ) : ℚ := (5 - 4 * alpha) / 3
def interiorXi (alpha : ℚ) : ℚ := 3 / 2 - alpha
def interiorTau (alpha : ℚ) : ℚ := interiorXi alpha / 2

def interiorANu (alpha nu : ℚ) : ℚ := interiorA alpha + 3 * nu
def interiorSigmaNu (alpha nu : ℚ) : ℚ := interiorSigma alpha - 2 * nu
def interiorGammaNu (alpha nu : ℚ) : ℚ := interiorGamma alpha - 4 * nu
def interiorXiNu (alpha nu : ℚ) : ℚ := interiorXi alpha - 3 * nu
def interiorTauNu (alpha nu : ℚ) : ℚ := interiorXiNu alpha nu / 2

/-- Gate 1 (`ν`-interior): the five shifted definitions are exactly the
parameters displayed in equation `margin-parameters`.  This is definitional
algebra and does not establish a Type-I or Type-II estimate. -/
theorem interior_margin_parameters_eq (alpha nu : ℚ) :
    interiorANu alpha nu = alpha - 1 + 3 * nu ∧
    interiorSigmaNu alpha nu = (2 - alpha) / 3 - 2 * nu ∧
    interiorGammaNu alpha nu = (5 - 4 * alpha) / 3 - 4 * nu ∧
    interiorXiNu alpha nu = 3 / 2 - alpha - 3 * nu ∧
    interiorTauNu alpha nu = (3 / 2 - alpha - 3 * nu) / 2 := by
  simp [interiorANu, interiorSigmaNu, interiorGammaNu, interiorXiNu,
    interiorTauNu, interiorA, interiorSigma, interiorGamma, interiorXi]

/-- Gate 1 (`ν`-interior): if the unshifted gap exceeds `5ν`, then
`[aν,σν]` is nonempty and its endpoints lie strictly inside
`(a+2ν,σ-4ν/3)`.  This proves only interval arithmetic, not Corollary 7.2. -/
theorem interior_typeII_interval_strict
    {alpha nu : ℚ} (hnu : 0 < nu)
    (hgap : 5 * nu < interiorSigma alpha - interiorA alpha) :
    interiorA alpha + 2 * nu < interiorANu alpha nu ∧
    interiorANu alpha nu < interiorSigmaNu alpha nu ∧
    interiorSigmaNu alpha nu < interiorSigma alpha - 4 * nu / 3 := by
  unfold interiorSigma interiorA at hgap
  unfold interiorANu interiorSigmaNu interiorA interiorSigma
  constructor
  · linarith
  constructor <;> linarith

/-- Gate 1 (exponent ledger): the shifted Type-I prefix plus `ξν` is exactly
`1/2-ν`, and the shifted prefix plus `γν` is `σ-2ν`, strictly below the
quoted upper interior endpoint.  These identities do not prove either
Grimmelt--Merikoski corollary. -/
theorem interior_exponent_ledger
    (alpha nu : ℚ) (hnu : 0 < nu) :
    (interiorA alpha + 2 * nu) + interiorXiNu alpha nu = 1 / 2 - nu ∧
    (interiorA alpha + 2 * nu) + interiorGammaNu alpha nu =
      interiorSigma alpha - 2 * nu ∧
    interiorSigma alpha - 2 * nu < interiorSigma alpha - 4 * nu / 3 := by
  unfold interiorA interiorXiNu interiorXi interiorGammaNu interiorGamma
    interiorSigma
  constructor
  · ring
  constructor
  · ring
  · linarith

/-- Gate 1 (`α<1.22` cutoff): on the retained range, `γ(α)>0.04` (and hence
`γ(α)≥0.04`).  This is a rational inequality only; it does not justify a
uniform analytic error term. -/
theorem gamma_gt_one_twenty_fifth
    {alpha : ℚ} (halpha : alpha < 122 / 100) :
    1 / 25 < interiorGamma alpha := by
  unfold interiorGamma
  linarith

/-- Gate 1 (`ν`-interior ordering): for `7/6<α<1.22` and a fixed positive
`ν` with `4ν<γ`, the shifted cutoffs satisfy
`0<γν<τν<a<σ`.  This is only affine order geometry and does not prove that
the external Type-I/II estimates are uniform on these cutoffs. -/
theorem interior_shifted_parameter_order
    {alpha nu : ℚ} (halphaLo : 7 / 6 < alpha)
    (halphaHi : alpha < 122 / 100) (hnu : 0 < nu)
    (hgamma : 4 * nu < interiorGamma alpha) :
    0 < interiorGammaNu alpha nu ∧
    interiorGammaNu alpha nu < interiorTauNu alpha nu ∧
    interiorTauNu alpha nu < interiorA alpha ∧
    interiorA alpha < interiorSigma alpha := by
  have hretained := gamma_gt_one_twenty_fifth halphaHi
  unfold interiorGamma at hretained
  unfold interiorGamma at hgamma
  unfold interiorGammaNu interiorGamma interiorTauNu interiorXiNu interiorXi
    interiorA interiorSigma
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Gate 1 (parameter ledger): the Type-II width `σ-a` is exactly `γ`.
This is the identity used to compare `5ν` with the unshifted gap. -/
theorem interior_sigma_sub_a (alpha : ℚ) :
    interiorSigma alpha - interiorA alpha = interiorGamma alpha := by
  unfold interiorSigma interiorA interiorGamma
  ring

/-- Gate 3 (prefix level): a prefix of exponent `s₀` plus remainder level
`1/2-s₀-ν` is exactly the common Type-I height `1/2-ν`.  This does not
apply Corollary 7.1. -/
theorem prefix_plus_remainder_level (s0 nu : ℚ) :
    s0 + (1 / 2 - s0 - nu) = 1 / 2 - nu := by
  ring

/-- Unconditional Selberg exponent recorded in Grimmelt--Merikoski
Corollary 7.1/7.2.  Recording the rational value does not prove those
corollaries. -/
def selbergTheta : ℚ := 7 / 64

/-- Gate 1 (error-exponent algebra): with `ε=η` the Type-I exponent in
the paper simplifies to `1-17η/32`.  This is rational arithmetic only. -/
theorem grimmelt_typeI_error_exponent (eta : ℚ) :
    1 - (1 - 2 * selbergTheta) * eta + eta / 4 =
      1 - 17 * eta / 32 := by
  unfold selbergTheta
  ring

/-- Gate 1 (error-exponent algebra): with `ε=η` the Type-II exponent
simplifies to `1-21η/32`. -/
theorem grimmelt_typeII_error_exponent (eta : ℚ) :
    1 - (1 - 2 * selbergTheta) * eta + eta / 8 =
      1 - 21 * eta / 32 := by
  unfold selbergTheta
  ring

/-- Gate 3 (`δ₀` algebra): the paper's choice `ε=ν` gives
`δ₀=17ν/32`.  Positivity of this rational does not bound `|r_P(e)|`. -/
theorem prefix_remainder_delta0 (nu : ℚ) :
    (1 - 2 * selbergTheta) * nu - nu / 4 = 17 * nu / 32 := by
  unfold selbergTheta
  ring

theorem prefix_remainder_delta0_pos {nu : ℚ} (hnu : 0 < nu) :
    0 < (1 - 2 * selbergTheta) * nu - nu / 4 := by
  rw [prefix_remainder_delta0]
  linarith

/-- Gate 3 (power-saving arithmetic): if `κ<2δ₀`, the collected-remainder
exponent `1-δ₀+κ/2` stays strictly below `1`.  This does not identify the
collected coefficient with Corollary 7.1. -/
theorem prefix_remainder_exponent_lt_one
    {delta0 kappa : ℚ} (_hdelta : 0 < delta0) (_hkappa : 0 ≤ kappa)
    (hgap : kappa < 2 * delta0) :
    1 - delta0 + kappa / 2 < 1 := by
  linarith

/-- At the left endpoint `α=7/6`, the unshifted one-prime tail cutoff is
`τ=1/6`, so three ordered primes have total exponent `1/2`. -/
theorem tau_at_seven_six : interiorTau (7 / 6) = 1 / 6 := by
  unfold interiorTau interiorXi
  norm_num

theorem three_tau_nu_at_seven_six (nu : ℚ) :
    3 * interiorTauNu (7 / 6) nu = 1 / 2 - 9 / 2 * nu := by
  unfold interiorTauNu interiorXiNu interiorXi
  ring

/-- Gate 3 (endpoint Type-I level): if the three-prime prefix stays at most
`3τ_ν` at `α=7/6`, the remainder height is at least `7ν/2`.  This keeps
`D` a positive power of `x` in the paper's algebra; it does not prove the
linear-sieve remainder estimate. -/
theorem three_prime_remainder_level_at_seven_six
    {s0 nu : ℚ} (hs0 : s0 ≤ 3 * interiorTauNu (7 / 6) nu) :
    7 / 2 * nu ≤ 1 / 2 - s0 - nu := by
  have h := three_tau_nu_at_seven_six nu
  linarith

end Landau
