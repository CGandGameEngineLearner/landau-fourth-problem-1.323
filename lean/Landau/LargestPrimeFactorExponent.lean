import Landau.HarmanRecursiveEndpoint
import Mathlib

namespace Landau

/-!
# Finite dyadic-block to pointwise exponent conversion

This module proves only the real-power inequality used after the analytic
block estimate has been supplied.  It does not formalize that analytic
estimate or the greatest-prime-factor theorem.
-/

/-- Gate 6 (endpoint assembly): a general real-power lemma converting a
left-endpoint block estimate into a slightly smaller pointwise exponent.  It
does not prove that the analytic block estimate holds. -/
theorem rpow_pointwise_lt_of_dyadic_scale_gap
    {x n a b : ℝ} (hx : 0 < x) (hn : 0 ≤ n) (hnx : n ≤ 2 * x)
    (ha : 0 ≤ a)
    (hscale : (2 : ℝ) ^ a < x ^ (b - a)) :
    n ^ a < x ^ b := by
  have hmono : n ^ a ≤ (2 * x) ^ a :=
    Real.rpow_le_rpow hn hnx ha
  calc
    n ^ a ≤ (2 * x) ^ a := hmono
    _ = (2 : ℝ) ^ a * x ^ a := by
      rw [Real.mul_rpow (by norm_num) hx.le]
    _ < x ^ (b - a) * x ^ a :=
      mul_lt_mul_of_pos_right hscale (Real.rpow_pos_of_pos hx a)
    _ = x ^ b := by
      rw [← Real.rpow_add hx]
      congr 1
      ring

/-- Gate 6 (endpoint assembly): the threshold `x > 2^13230` supplies exactly
the scale gap between `1.323` and `1.3231`.  It proves no greatest-prime-factor
statement. -/
theorem recursive_dyadic_scale_gap_of_threshold
    {x : ℝ} (hx : (2 : ℝ) ^ (13230 : ℕ) < x) :
    (2 : ℝ) ^ (recursiveSwitchingPointwiseExponent : ℝ) <
      x ^ ((recursiveSwitchingBlockExponent : ℝ) -
        recursiveSwitchingPointwiseExponent) := by
  have hpow : (2 : ℝ) ^ (13230 : ℝ) < x := by
    calc
      (2 : ℝ) ^ (13230 : ℝ) = (2 : ℝ) ^ (13230 : ℕ) :=
        Real.rpow_natCast (2 : ℝ) 13230
      _ < x := hx
  have hroot := Real.rpow_lt_rpow
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (13230 : ℝ))
    hpow (by norm_num : (0 : ℝ) < 1 / 10000)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hroot
  norm_num [recursiveSwitchingPointwiseExponent,
    recursiveSwitchingBlockExponent] at hroot ⊢
  exact hroot

/-- Gate 6 (endpoint assembly): the exact finite real-power conversion used
in the final paragraph of the paper.  It assumes the dyadic block setup and
does not prove the analytic block estimate or the main theorem. -/
theorem recursive_pointwise_rpow_lt_of_dyadic_block
    {x n : ℝ} (hx : (2 : ℝ) ^ (13230 : ℕ) < x)
    (hn : 0 ≤ n) (hnx : n ≤ 2 * x) :
    n ^ (recursiveSwitchingPointwiseExponent : ℝ) <
      x ^ (recursiveSwitchingBlockExponent : ℝ) := by
  have hxpos : 0 < x :=
    lt_trans (by positivity : (0 : ℝ) < (2 : ℝ) ^ (13230 : ℕ)) hx
  exact rpow_pointwise_lt_of_dyadic_scale_gap hxpos hn hnx
    (by norm_num [recursiveSwitchingPointwiseExponent])
    (recursive_dyadic_scale_gap_of_threshold hx)

end Landau
