import Landau.HarmanRecursiveCertificateValue0
import Landau.HarmanRecursiveCertificateValue1
import Landau.HarmanRecursiveCertificateValue2
import Landau.HarmanRecursiveCertificateValue3
import Landau.HarmanIntegerRounding
import Landau.PublishedHarmanConstants
import Landau.HarmanRecursiveEndpoint

namespace Landau

/-!
The final aggregation deliberately projects the five certified block values
before adding them.  Rewriting the nested `RecursiveCertificateData` value in
one shot makes Lean instantiate all four native computations simultaneously
and uses far more memory than the certificate itself requires.  The block
equalities imported below use `native_decide`; the aggregation in this file
is exact natural-number and rational arithmetic checked without re-running
the block evaluator.
-/

def canonicalRecursiveCertificateSavingSum : Nat :=
  recursiveCertificateBlock0Saving +
  recursiveCertificateBlock1Saving +
  recursiveCertificateBlock2Saving +
  recursiveCertificateBlock3Saving +
  recursiveCertificateZeroTailSaving

theorem canonical_recursive_certificate_saving_sum :
    canonicalRecursiveCertificateSavingSum = 465165906793678 := by
  norm_num [canonicalRecursiveCertificateSavingSum,
    recursiveCertificateBlock0Saving, recursiveCertificateBlock1Saving,
    recursiveCertificateBlock2Saving, recursiveCertificateBlock3Saving,
    recursiveCertificateZeroTailSaving]

def canonicalRecursiveCertificateSaving : Nat :=
  canonicalRecursiveCertificateSavingSum / (12 * 1200)

theorem canonical_recursive_certificate_saving :
    canonicalRecursiveCertificateSaving = 32303187971 := by
  rw [canonicalRecursiveCertificateSaving, canonical_recursive_certificate_saving_sum]

/-- The Lean-recomputed recursive certificate strictly exceeds the
`0.032` target used by the exact `1.3231` endpoint budget. -/
theorem recursive_certificate_exceeds_target :
    recursiveSwitchingSavingTarget <
      (canonicalRecursiveCertificateSaving : ℚ) / scale := by
  rw [canonical_recursive_certificate_saving]
  norm_num [recursiveSwitchingSavingTarget, scale]

/-- Exact rational saving represented by the downward-rounded canonical
certificate. -/
def canonicalRecursiveCertificateSavingRational : ℚ :=
  (canonicalRecursiveCertificateSaving : ℚ) / scale

theorem canonical_recursive_certificate_saving_rational :
    canonicalRecursiveCertificateSavingRational =
      32303187971 / 1000000000000 := by
  rw [canonicalRecursiveCertificateSavingRational,
    canonical_recursive_certificate_saving]
  norm_num [scale]

/-- The complete core envelope after substituting the certified saving,
rather than merely the conservative `0.032` target. -/
def certifiedRecursiveCoreEnvelope : ℚ :=
  1 / 6 + publishedF1Upper + publishedF2Upper + publishedF3Upper +
    publishedF4Upper + publishedF5 - switchedF6Lower -
      canonicalRecursiveCertificateSavingRational

/-- Gate 6 (endpoint assembly): exact core constant displayed in equation
`core` of the paper.  This is rational arithmetic and does not prove that
the quoted analytic component bounds apply. -/
theorem certified_recursive_core_envelope_eq :
    certifiedRecursiveCoreEnvelope =
      5611320508261 / 9000000000000 := by
  rw [certifiedRecursiveCoreEnvelope,
    canonical_recursive_certificate_saving_rational]
  norm_num [publishedF1Upper, publishedF2Upper, publishedF3Upper,
    publishedF4Upper, publishedF5, switchedF6Lower]

/-- Gate 6 (endpoint assembly): the core is assembled as the five positive
published terms plus `1/6`, followed by exactly one subtraction of the `F₆`
constant and exactly one subtraction of the recursive saving.  This
definitional identity does not validate any analytic input. -/
theorem certified_recursive_core_assembly_once :
    certifiedRecursiveCoreEnvelope =
      1 / 6 + publishedF1Upper + publishedF2Upper + publishedF3Upper +
        publishedF4Upper + publishedF5 - switchedF6Lower -
          canonicalRecursiveCertificateSavingRational := by
  rfl

/-- Gate 6 (endpoint assembly): adding back one `F₆` constant and one saving
recovers the positive core, so neither term is subtracted twice.  This is
only an additive rational identity. -/
theorem certified_recursive_core_no_double_subtraction :
    certifiedRecursiveCoreEnvelope + switchedF6Lower +
        canonicalRecursiveCertificateSavingRational =
      1 / 6 + publishedF1Upper + publishedF2Upper + publishedF3Upper +
        publishedF4Upper + publishedF5 := by
  rw [certified_recursive_core_assembly_once]
  ring

/-- Exact endpoint total and its strict positive margin at internal block
exponent `1.3231`. -/
theorem certified_recursive_endpoint_budget :
    certifiedRecursiveCoreEnvelope +
      2 * (recursiveSwitchingBlockExponent ^ 2 - (5 / 4 : ℚ) ^ 2) =
        8997005488261 / 9000000000000 ∧
    1 - (certifiedRecursiveCoreEnvelope +
      2 * (recursiveSwitchingBlockExponent ^ 2 - (5 / 4 : ℚ) ^ 2)) =
        2994511739 / 9000000000000 ∧
    certifiedRecursiveCoreEnvelope +
      2 * (recursiveSwitchingBlockExponent ^ 2 - (5 / 4 : ℚ) ^ 2) < 1 := by
  rw [certifiedRecursiveCoreEnvelope,
    canonical_recursive_certificate_saving_rational]
  norm_num [recursiveSwitchingBlockExponent, publishedF1Upper,
    publishedF2Upper, publishedF3Upper, publishedF4Upper, publishedF5,
    switchedF6Lower]

end Landau
