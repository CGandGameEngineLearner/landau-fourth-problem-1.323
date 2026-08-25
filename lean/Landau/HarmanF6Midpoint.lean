import Landau.PublishedHarmanConstants
import Mathlib

namespace Landau

open MeasureTheory Set
open scoped Interval

/-!
# The elementary ten-panel lower certificate for `F₆`

This module formalizes the finite calculus and rational midpoint computation
in Lemma `F6` of the paper.  The Buchstab-function estimate
`ω(u) ≥ 0.5607` on the stated range remains an external analytic input.
-/

/-- The elementary width after the substitution `u = α/β - 1`. -/
def g6WidthQ (alpha : ℚ) : ℚ :=
  1 / (alpha - 1) + 4 - 6 / (2 - alpha)

/-- Real version of the width occurring in the integral. -/
noncomputable def g6WidthR (alpha : ℝ) : ℝ :=
  1 / (alpha - 1) + 4 - 6 / (2 - alpha)

/-- The exact ten-panel midpoint lower sum on `[7/6,5/4]`. -/
def g6MidpointArea10 : ℚ :=
  ∑ j ∈ Finset.range 10,
    (1 / 120 : ℚ) *
      g6WidthQ ((7 / 6 : ℚ) + ((2 * j + 1 : ℕ) : ℚ) / 240)

/-- Gate 6 (endpoint assembly): exact rational computation behind the
displayed midpoint lower bound.  It does not prove the quoted Buchstab lower
bound or identify the width integral with the original sifted sum. -/
theorem g6_midpoint_area_ten_certifies_lower_bound :
    switchedF6Lower < (5607 / 10000 : ℚ) * g6MidpointArea10 := by
  norm_num [g6MidpointArea10, g6WidthQ, switchedF6Lower,
    Finset.sum_range_succ]

/-- Gate 6 (endpoint assembly): first-derivative identity used only for the
finite convexity proof; it proves no Buchstab-function estimate. -/
private theorem g6WidthR_hasDerivAt {x : ℝ} (h1 : x ≠ 1) (h2 : x ≠ 2) :
    HasDerivAt g6WidthR (-1 / (x - 1)^2 - 6 / (2-x)^2) x := by
  unfold g6WidthR
  convert (((hasDerivAt_const x 1).div ((hasDerivAt_id x).sub_const 1)
    (sub_ne_zero.mpr h1)).add_const 4).sub
      ((hasDerivAt_const x 6).div ((hasDerivAt_const x 2).sub (hasDerivAt_id x))
        (sub_ne_zero.mpr h2.symm)) using 1
  field_simp

/-- Gate 6 (endpoint assembly): second-derivative identity used only for the
finite convexity proof; it proves no analytic sieve transfer. -/
private theorem g6WidthR_deriv_hasDerivAt {x : ℝ} (h1 : x ≠ 1) (h2 : x ≠ 2) :
    HasDerivAt (fun x : ℝ => -1 / (x - 1)^2 - 6 / (2-x)^2)
      (2 / (x-1)^3 - 12 / (2-x)^3) x := by
  convert ((hasDerivAt_const x (-1)).div
    (((hasDerivAt_id x).sub_const 1).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr h1))).sub
    ((hasDerivAt_const x 6).div
      (((hasDerivAt_const x 2).sub (hasDerivAt_id x)).pow 2)
        (pow_ne_zero 2 (sub_ne_zero.mpr h2.symm))) using 1
  field_simp [sub_ne_zero.mpr h1, sub_ne_zero.mpr h2.symm]
  ring

/-- Gate 6 (endpoint assembly): the displayed second derivative of `w` is
strictly positive throughout the closed interval used by Lemma `F6`.  This
does not prove the external lower bound for the Buchstab function. -/
theorem g6_width_second_derivative_pos {x : ℝ}
    (hx : x ∈ Icc (7/6 : ℝ) (5/4 : ℝ)) :
    0 < 2 / (x - 1)^3 - 12 / (2-x)^3 := by
  have hdpos : 0 < x - 1 := by rcases hx with ⟨hx, _⟩; norm_num at hx ⊢; linarith
  have hdle : x - 1 ≤ (1/4 : ℝ) := by rcases hx with ⟨_, hx⟩; norm_num at hx ⊢; linarith
  have hepos : 0 < 2 - x := by rcases hx with ⟨_, hx⟩; norm_num at hx ⊢; linarith
  have hele : (3/4 : ℝ) ≤ 2 - x := by rcases hx with ⟨_, hx⟩; norm_num at hx ⊢; linarith
  have hfirst : (128 : ℝ) ≤ 2 / (x - 1)^3 := by
    calc
      (128 : ℝ) = 2 / (1/4 : ℝ)^3 := by norm_num
      _ ≤ 2 / (x-1)^3 := by gcongr
  have hsecond : 12 / (2-x)^3 ≤ (768/27 : ℝ) := by
    calc
      12 / (2-x)^3 ≤ 12 / (3/4 : ℝ)^3 := by gcongr
      _ = (768/27 : ℝ) := by norm_num
  linarith

/-- Gate 6 (endpoint assembly): continuity of the elementary rational width;
this does not formalize the analytic origin of `F₆`. -/
theorem g6WidthR_continuousOn :
    ContinuousOn g6WidthR (Icc (7/6 : ℝ) (5/4 : ℝ)) := by
  intro x hx
  have h1 : x - 1 ≠ 0 := by rcases hx with ⟨hx, _⟩; norm_num at hx ⊢; linarith
  have h2 : 2 - x ≠ 0 := by rcases hx with ⟨_, hx⟩; norm_num at hx ⊢; linarith
  unfold g6WidthR
  exact (((continuousAt_const.div
    (continuousAt_id.sub continuousAt_const) h1).add continuousAt_const).sub
    (continuousAt_const.div
      (continuousAt_const.sub continuousAt_id) h2)).continuousWithinAt

/-- Gate 6 (endpoint assembly): convexity of the elementary width on the
complete `F₆` interval.  It does not prove a statement about `ω`. -/
theorem g6WidthR_convexOn :
    ConvexOn ℝ (Icc (7/6 : ℝ) (5/4 : ℝ)) g6WidthR := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc (7/6 : ℝ) (5/4 : ℝ))
  · exact g6WidthR_continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have h1 : x ≠ 1 := by norm_num at hx ⊢; linarith
    have h2 : x ≠ 2 := by norm_num at hx ⊢; linarith
    exact (g6WidthR_hasDerivAt h1 h2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h1 : x ≠ 1 := by norm_num at hx ⊢; linarith
    have h2 : x ≠ 2 := by norm_num at hx ⊢; linarith
    exact (g6WidthR_deriv_hasDerivAt h1 h2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (g6_width_second_derivative_pos ⟨hx.1.le, hx.2.le⟩).le

/-- Gate 6 (endpoint assembly): Jensen's inequality specialized to a
midpoint on a real interval.  It is a finite-calculus lemma, not a sieve
estimate. -/
theorem convex_midpoint_mul_width_le_integral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfconv : ConvexOn ℝ (Icc a b) f)
    (hfcont : ContinuousOn f (Icc a b)) :
    (b-a) * f ((a+b)/2) ≤ ∫ x in a..b, f x := by
  have hzero : volume (Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have htop : volume (Ioc a b) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hidmem : ∀ᵐ x ∂volume.restrict (Ioc a b), x ∈ Icc a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact ⟨hx.1.le, hx.2⟩
  have hidint : IntegrableOn (fun x : ℝ => x) (Ioc a b) volume :=
    continuous_id.integrableOn_Ioc
  have hfint : IntegrableOn (f ∘ fun x : ℝ => x) (Ioc a b) volume := by
    simpa only [Function.comp_id] using
      hfcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hj := hfconv.map_set_average_le hfcont isClosed_Icc hzero htop
    hidmem hidint hfint
  have hj' : f (⨍ x in a..b, x) ≤ ⨍ x in a..b, f x := by
    simpa [uIoc_of_le hab.le] using hj
  rw [interval_average_eq_div, interval_average_eq_div, integral_id] at hj'
  have havg : ((b^2-a^2)/2)/(b-a) = (a+b)/2 := by
    apply (div_eq_iff (sub_ne_zero.mpr hab.ne')).2
    ring
  rw [havg] at hj'
  have hmul := (le_div_iff₀ (sub_pos.mpr hab)).mp hj'
  simpa [mul_comm] using hmul

private noncomputable def g6Panel (j : ℕ) : ℝ := 7/6 + j/120

/-- Gate 6 (endpoint assembly): convexity makes the complete ten-panel
midpoint sum a lower bound for the real width integral.  This does not yet
apply the external Buchstab lower bound. -/
theorem g6_midpoint_sum_le_integral :
    (1/120 : ℝ) * (∑ j ∈ Finset.range 10,
      g6WidthR ((7/6 : ℝ) + ((2*j+1 : ℕ) : ℝ)/240)) ≤
      ∫ x in (7/6 : ℝ)..(5/4 : ℝ), g6WidthR x := by
  have hpanel : ∀ j < 10,
      (1/120 : ℝ) * g6WidthR
        ((7/6 : ℝ) + ((2*j+1 : ℕ) : ℝ)/240) ≤
        ∫ x in g6Panel j..g6Panel (j+1), g6WidthR x := by
    intro j hj
    have hsub : Icc (g6Panel j) (g6Panel (j+1)) ⊆
        Icc (7/6 : ℝ) (5/4 : ℝ) := by
      intro x hx
      have hjnext : ((j+1 : ℕ) : ℝ) ≤ 10 := by
        exact_mod_cast Nat.succ_le_of_lt hj
      dsimp [g6Panel] at hx
      push_cast at hx hjnext
      constructor <;> norm_num at hx hjnext ⊢ <;> linarith
    have hab : g6Panel j < g6Panel (j+1) := by
      dsimp [g6Panel]
      push_cast
      linarith
    have h := convex_midpoint_mul_width_le_integral hab
      (g6WidthR_convexOn.subset hsub (convex_Icc _ _))
      (g6WidthR_continuousOn.mono hsub)
    convert h using 1
    all_goals dsimp [g6Panel]
    all_goals push_cast
    all_goals ring_nf
  calc
    (1/120 : ℝ) * (∑ j ∈ Finset.range 10,
        g6WidthR ((7/6 : ℝ) + ((2*j+1 : ℕ) : ℝ)/240)) =
        ∑ j ∈ Finset.range 10,
          (1/120 : ℝ) * g6WidthR
            ((7/6 : ℝ) + ((2*j+1 : ℕ) : ℝ)/240) := by
            rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range 10,
        ∫ x in g6Panel j..g6Panel (j+1), g6WidthR x := by
      exact Finset.sum_le_sum fun j hj => hpanel j (Finset.mem_range.mp hj)
    _ = ∫ x in g6Panel 0..g6Panel 10, g6WidthR x := by
      apply intervalIntegral.sum_integral_adjacent_intervals
      intro j hj
      apply ContinuousOn.intervalIntegrable
      exact g6WidthR_continuousOn.mono (by
        intro x hx
        have hab : g6Panel j ≤ g6Panel (j+1) := by
          dsimp [g6Panel]
          push_cast
          linarith
        rw [uIcc_of_le hab] at hx
        have hjnext : ((j+1 : ℕ) : ℝ) ≤ 10 := by
          exact_mod_cast Nat.succ_le_of_lt hj
        dsimp [g6Panel] at hx
        push_cast at hx hjnext
        constructor <;> norm_num at hx hjnext ⊢ <;> linarith)
    _ = ∫ x in (7/6 : ℝ)..(5/4 : ℝ), g6WidthR x := by
      norm_num [g6Panel]

/-- Gate 6 (endpoint assembly): fully formal finite-calculus certificate for
the paper's `F₆` lower constant.  Applying it to `F₆` itself additionally
uses the external Buchstab estimate `ω(u) ≥ 0.5607`. -/
theorem g6_width_integral_certified :
    (switchedF6Lower : ℝ) <
      (5607/10000 : ℝ) *
        ∫ x in (7/6 : ℝ)..(5/4 : ℝ), g6WidthR x := by
  have hnum : (switchedF6Lower : ℝ) <
      (5607/10000 : ℝ) * ((1/120 : ℝ) *
        (∑ j ∈ Finset.range 10,
          g6WidthR ((7/6 : ℝ) + ((2*j+1 : ℕ) : ℝ)/240))) := by
    norm_num [switchedF6Lower, g6WidthR, Finset.sum_range_succ]
  exact hnum.trans_le (mul_le_mul_of_nonneg_left
    g6_midpoint_sum_le_integral (by norm_num))

end Landau
