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

end Landau
