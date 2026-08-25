import Landau.LinearSieveRationalEnvelope
import Landau.PublishedHarmanConstants

namespace Landau

/-!
# Exact endpoint arithmetic for the recursive `1.323` certificate

This module records the exact finite arithmetic after the recursive integer
certificate supplies a saving of at least `0.032`. The analytic transfer from
the cited Type-I/II estimates and linear sieve remains an external input, as
stated in the paper.
-/

/-- Conservative saving target certified by the recursive integer certificate. -/
def recursiveSwitchingSavingTarget : ℚ := 4 / 125

/-- Internal dyadic block exponent, leaving a strict pointwise margin. -/
def recursiveSwitchingBlockExponent : ℚ := 13231 / 10000

/-- Pointwise exponent obtained after the certified block margin. -/
def recursiveSwitchingPointwiseExponent : ℚ := 1323 / 1000

/-- Core envelope with the recursive target substituted for the current
three-step certificate. -/
def recursiveSwitchingTargetCoreEnvelope : ℚ :=
  1 / 6 + publishedF1Upper + publishedF2Upper + publishedF3Upper +
    publishedF4Upper + publishedF5 - switchedF6Lower -
      recursiveSwitchingSavingTarget

/-- Exact normalized endpoint budget.  This is deliberately a target
calculation: the missing premise is a certified analytic saving at least
`recursiveSwitchingSavingTarget`. -/
theorem recursive_switching_target_endpoint_budget :
    recursiveSwitchingTargetCoreEnvelope +
      2 * (recursiveSwitchingBlockExponent ^ 2 - (5 / 4 : ℚ) ^ 2) =
        449986709 / 450000000 ∧
    recursiveSwitchingTargetCoreEnvelope +
      2 * (recursiveSwitchingBlockExponent ^ 2 - (5 / 4 : ℚ) ^ 2) < 1 := by
  norm_num [recursiveSwitchingTargetCoreEnvelope,
    recursiveSwitchingSavingTarget, recursiveSwitchingBlockExponent,
    publishedF1Upper, publishedF2Upper, publishedF3Upper,
    publishedF4Upper, publishedF5, switchedF6Lower]

/-- The internal block exponent is strictly above the stated pointwise
exponent. The analytic dyadic passage itself is external to this project. -/
theorem recursive_switching_block_gt_pointwise :
    recursiveSwitchingPointwiseExponent < recursiveSwitchingBlockExponent := by
  norm_num [recursiveSwitchingPointwiseExponent,
    recursiveSwitchingBlockExponent]

/-- The proposed pointwise exponent strictly improves Li's `1.317`
comparison frontier. -/
theorem recursive_switching_pointwise_gt_published_frontier :
    (1317 / 1000 : ℚ) < recursiveSwitchingPointwiseExponent := by
  norm_num [recursiveSwitchingPointwiseExponent]

/-- With the conservative manuscript constants, reaching `4/3` requires
this exact switching saving. -/
def switchingSavingNeededForFourThirds : ℚ := 215847 / 2500000

theorem recursive_target_short_of_four_thirds :
    recursiveSwitchingSavingTarget < switchingSavingNeededForFourThirds ∧
    switchingSavingNeededForFourThirds - recursiveSwitchingSavingTarget =
      135847 / 2500000 := by
  norm_num [recursiveSwitchingSavingTarget,
    switchingSavingNeededForFourThirds]

end Landau
