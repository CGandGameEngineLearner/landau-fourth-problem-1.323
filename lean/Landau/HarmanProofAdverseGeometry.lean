import Landau.HarmanRecursiveCertificate

namespace Landau

open Set

/-!
# Gate 4: one-sided, proof-adverse cell geometry

Every theorem in this file addresses publication-review gate 4.  The results
check endpoint identities, interval containments, and the Boolean branches of
the integer certificate.  They do **not** prove that a Type-II estimate, a
linear-sieve estimate, or any limiting integral is valid on those cells.
-/

def alphaCellLoQ (n i : Nat) : ℚ := (14 * n + i : Nat) / (12 * n : Nat)
def alphaCellHiQ (n i : Nat) : ℚ := (14 * n + i + 1 : Nat) / (12 * n : Nat)
def switchingGammaQ (alpha : ℚ) : ℚ := (5 - 4 * alpha) / 3
def switchingTauQ (alpha : ℚ) : ℚ := (3 / 2 - alpha) / 2

/-- Gate 4 (common lower domain): the first common-grid endpoint is exactly
`γ(α_lo)`.  This is an integer/rational identity only; it does not prove a
lower bound for `A₁` or `A₃`. -/
theorem commonBetaNum_zero_eq_gamma_lo
    {n b i : Nat} (hn : 0 < n) (hb : 0 < b) (hi : i ≤ n) :
    ((commonBetaNum n b i 0 : Nat) : ℚ) / (72 * n * b : Nat) =
      switchingGammaQ (alphaCellLoQ n i) := by
  rw [commonBetaNum]
  unfold switchingGammaQ alphaCellLoQ
  push_cast [Nat.cast_sub hi]
  field_simp
  ring

/-- Gate 4 (common lower domain): the last common-grid endpoint is exactly
`τ(α_hi)`.  This checks the claimed common subdomain endpoint, not an
analytic Riemann-sum inequality. -/
theorem commonBetaNum_last_eq_tau_hi
    {n b i : Nat} (hn : 0 < n) (hb : 0 < b) (hi : i + 1 ≤ n) :
    ((commonBetaNum n b i b : Nat) : ℚ) / (72 * n * b : Nat) =
      switchingTauQ (alphaCellHiQ n i) := by
  rw [commonBetaNum]
  have hin : i ≤ n := le_trans (Nat.le_add_right i 1) hi
  have hwidth : 3 ≤ 4 * n + 5 * i := by omega
  unfold switchingTauQ alphaCellHiQ
  push_cast [Nat.cast_sub hin, Nat.cast_sub hwidth]
  field_simp
  ring

/-- Gate 4 (containing upper domain): the first containing-grid endpoint is
exactly `γ(α_hi)`.  This is a containment endpoint identity only; it does not
prove the upper estimate used on the domain. -/
theorem containingBetaNum_zero_eq_gamma_hi
    {n b i : Nat} (hn : 0 < n) (hb : 0 < b) (hi : i + 1 ≤ n) :
    ((containingBetaNum n b i 0 : Nat) : ℚ) / (72 * n * b : Nat) =
      switchingGammaQ (alphaCellHiQ n i) := by
  rw [containingBetaNum]
  have hsub : i + 1 ≤ n := hi
  rw [show n - i - 1 = n - (i + 1) by omega]
  unfold switchingGammaQ alphaCellHiQ
  push_cast [Nat.cast_sub hsub]
  field_simp
  ring

/-- Gate 4 (containing upper domain): the last containing-grid endpoint is
exactly `τ(α_lo)`.  This verifies the containing superdomain endpoint, not
the analytic upper integral. -/
theorem containingBetaNum_last_eq_tau_lo
    {n b i : Nat} (hn : 0 < n) (hb : 0 < b) (hi : i + 1 ≤ n) :
    ((containingBetaNum n b i b : Nat) : ℚ) / (72 * n * b : Nat) =
      switchingTauQ (alphaCellLoQ n i) := by
  rw [containingBetaNum]
  rw [show n - i - 1 = n - (i + 1) by omega]
  have hwidth : 3 ≤ 4 * n + 5 * i + 8 := by omega
  unfold switchingTauQ alphaCellLoQ
  push_cast [Nat.cast_sub hi, Nat.cast_sub hwidth]
  field_simp
  ring

/-- Gate 4 (common lower domain): for every `α` in its cell, the common
interval `[γ(α_lo),τ(α_hi)]` is contained in the analytic interval
`[γ(α),τ(α)]`.  This proves only affine interval geometry. -/
theorem common_domain_subset_analytic_domain
    {alphaLo alphaHi alpha : ℚ}
    (ha : alphaLo ≤ alpha) (hb : alpha ≤ alphaHi) :
    Icc (switchingGammaQ alphaLo) (switchingTauQ alphaHi) ⊆
      Icc (switchingGammaQ alpha) (switchingTauQ alpha) := by
  intro beta hbeta
  rcases hbeta with ⟨hbetaLo, hbetaHi⟩
  constructor
  · dsimp [switchingGammaQ] at hbetaLo ⊢
    linarith
  · dsimp [switchingTauQ] at hbetaHi ⊢
    linarith

/-- Gate 4 (containing upper domain): for every `α` in its cell, the
analytic interval `[γ(α),τ(α)]` is contained in
`[γ(α_hi),τ(α_lo)]`.  This proves only affine interval geometry. -/
theorem analytic_domain_subset_containing_domain
    {alphaLo alphaHi alpha : ℚ}
    (ha : alphaLo ≤ alpha) (hb : alpha ≤ alphaHi) :
    Icc (switchingGammaQ alpha) (switchingTauQ alpha) ⊆
      Icc (switchingGammaQ alphaHi) (switchingTauQ alphaLo) := by
  intro beta hbeta
  rcases hbeta with ⟨hbetaLo, hbetaHi⟩
  constructor
  · dsimp [switchingGammaQ] at hbetaLo ⊢
    linarith
  · dsimp [switchingTauQ] at hbetaHi ⊢
    linarith

/-- Gate 4 (`A₃` lower direction): when the complete pair cell lies inside
`[aMax,sigmaMin]`, the code seeds the entire clipped third-prime domain with
`omegaLower`.  The subsequent threshold fold is shown syntactically; this
does not prove Corollary 7.2 or the lower-sieve estimate. -/
theorem thirdPrimeLowerIntervals_full_pair_branch
    (b1 b2 : ExponentCell) (domainLo domainHi aMax sigmaMin half : Nat)
    (hpair : aMax ≤ b1.lo + b2.lo ∧ b1.hi + b2.hi ≤ sigmaMin) :
    thirdPrimeLowerIntervals b1 b2 domainLo domainHi aMax sigmaMin half =
      sieveThresholds.foldl (fun xs threshold =>
        let residual := half - b1.hi - b2.hi
        let upper := threshold.q * residual / (threshold.p + threshold.q)
        addWeightedClipped domainLo upper threshold.weight domainLo domainHi xs)
        (addWeightedClipped domainLo domainHi omegaLower domainLo domainHi []) := by
  simp [thirdPrimeLowerIntervals, hpair]

/-- Gate 4 (`A₃` lower direction): if the full pair cell is not Type II,
the `omegaLower` seed consists only of the three common subset-sum
subintervals before lower-sieve thresholds are added.  This is a code-branch
identity, not an analytic Type-II theorem. -/
theorem thirdPrimeLowerIntervals_subset_branches
    (b1 b2 : ExponentCell) (domainLo domainHi aMax sigmaMin half : Nat)
    (hpair : ¬(aMax ≤ b1.lo + b2.lo ∧ b1.hi + b2.hi ≤ sigmaMin)) :
    thirdPrimeLowerIntervals b1 b2 domainLo domainHi aMax sigmaMin half =
      let xs := addWeightedClipped (aMax - b1.lo) (sigmaMin - b1.hi)
        omegaLower domainLo domainHi []
      let xs := addWeightedClipped (aMax - b2.lo) (sigmaMin - b2.hi)
        omegaLower domainLo domainHi xs
      let xs := addWeightedClipped (aMax - b1.lo - b2.lo)
        (sigmaMin - b1.hi - b2.hi) omegaLower domainLo domainHi xs
      let residual := half - b1.hi - b2.hi
      sieveThresholds.foldl (fun xs threshold =>
        let upper := threshold.q * residual / (threshold.p + threshold.q)
        addWeightedClipped domainLo upper threshold.weight domainLo domainHi xs) xs := by
  simp [thirdPrimeLowerIntervals, hpair]

/-- Gate 4 (two-prime upper direction): on a complete Type-II pair cell,
`pairChildUpper` takes the minimum of the universal `U_LS` fixed-point upper
bound and the direct `u₊/β₂` upper bound.  This unfolds the Boolean gate; it
does not prove either analytic upper bound. -/
theorem pairChildUpper_typeII_branch
    (ab : RecursiveAlphaBounds) (b1 b2 : ExponentCell)
    (hb20 : 0 < b2.lo) (hb2 : b2.lo < b2.hi)
    (hdelta : scale / 2 - (b1.hi + b2.hi) ≠ 0)
    (hpair : ab.aMax ≤ b1.lo + b2.lo ∧
      b1.hi + b2.hi ≤ ab.sigmaMin) :
    pairChildUpper ab b1 b2 = some (min
      (max (ceilScaled (2 * scale) (scale / 2 - (b1.hi + b2.hi)))
        (ceilScaled (2 * scale) (3 * b2.lo)))
      (ceilScaled omegaUpper b2.lo)) := by
  simp [pairChildUpper, hb20, hb2, hdelta, hpair]

/-- Gate 4 (recursive two-prime upper direction): the base-minus-children
candidate is enabled only under the `β₁+β₂≤ξ`, positive-base, ordered-domain,
and `childrenLower≤baseUpper` gates.  This is an exact program equation and
does not prove the analytic validity of the candidates. -/
theorem pairChildUpper_recursive_branch
    (ab : RecursiveAlphaBounds) (b1 b2 : ExponentCell)
    (hb20 : 0 < b2.lo) (hb2 : b2.lo < b2.hi)
    (hdelta : scale / 2 - (b1.hi + b2.hi) ≠ 0)
    (hpair : ¬(ab.aMax ≤ b1.lo + b2.lo ∧
      b1.hi + b2.hi ≤ ab.sigmaMin))
    (hxi : b1.hi + b2.hi ≤ ab.xiMin)
    (hgamma : 0 < ab.gammaMin) (hdom : ab.gammaMax < b2.lo)
    (hchildren : weightedReciprocalLower
      (thirdPrimeLowerIntervals b1 b2 ab.gammaMax b2.lo
        ab.aMax ab.sigmaMin (scale / 2)) scale ≤
      ceilScaled omegaUpper ab.gammaMin) :
    pairChildUpper ab b1 b2 = some (min
      (max (ceilScaled (2 * scale) (scale / 2 - (b1.hi + b2.hi)))
        (ceilScaled (2 * scale) (3 * b2.lo)))
      (ceilScaled omegaUpper ab.gammaMin -
        weightedReciprocalLower
          (thirdPrimeLowerIntervals b1 b2 ab.gammaMax b2.lo
            ab.aMax ab.sigmaMin (scale / 2)) scale)) := by
  simp [pairChildUpper, hb20, hb2, hdelta, hpair, hxi, hgamma, hdom,
    hchildren]

/-- Gate 4 (tail upper domain): the child mesh starts exactly at
`gammaMin`.  This endpoint fact does not prove an upper integral estimate. -/
theorem tail_child_grid_starts_at_gammaMin
    (ab : RecursiveAlphaBounds) (b1 : ExponentCell) (steps : Nat) :
    (equalExponentCell ab.gammaMin b1.hi 0 steps).lo = ab.gammaMin := by
  simp [equalExponentCell]

/-- Gate 4 (tail upper domain): for a positive number of steps, the final
child cell ends at `b1.hi`; hence the containing mesh includes the same
`β₁` cell and the proof-adverse `β₂≥β₁` portion.  This is only a finite-grid
containment statement, not the analytic upper bound for the child sum. -/
theorem tail_child_grid_ends_at_b1_hi
    (ab : RecursiveAlphaBounds) (b1 : ExponentCell) {steps : Nat}
    (hsteps : 0 < steps) (horder : ab.gammaMin ≤ b1.hi) :
    (equalExponentCell ab.gammaMin b1.hi (steps - 1) steps).hi = b1.hi := by
  simp [equalExponentCell]
  have hs : steps - 1 + 1 = steps := by omega
  rw [hs, Nat.mul_div_left _ hsteps]
  omega

/-- Gate 4 (tail upper direction): under the natural endpoint order, the
entire same `β₁` cell lies in the containing child domain
`[gammaMin,b1.hi]`.  This proves the intended overcoverage only. -/
theorem same_beta_cell_subset_tail_child_domain
    (ab : RecursiveAlphaBounds) (b1 : ExponentCell)
    (hgamma : ab.gammaMin ≤ b1.lo) :
    Set.Icc b1.lo b1.hi ⊆ Set.Icc ab.gammaMin b1.hi := by
  intro beta hbeta
  exact ⟨le_trans hgamma hbeta.1, hbeta.2⟩

end Landau
