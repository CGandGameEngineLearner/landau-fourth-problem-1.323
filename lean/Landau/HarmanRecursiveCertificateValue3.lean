import Landau.HarmanRecursiveCertificateBlock3

namespace Landau

def recursiveCertificateBlock3Saving : Nat := 41925800002266

theorem recursive_certificate_block3_saving :
    (recursiveCertificateDataRange 1200 300 160 576 192).savingSum =
      recursiveCertificateBlock3Saving := by
  change (recursiveCertificateDataRange 1200 300 160 576 192).savingSum =
    41925800002266
  exact congrArg RecursiveCertificateData.savingSum recursive_certificate_block3

def recursiveCertificateZeroTailSaving : Nat := 0

theorem recursive_certificate_zero_tail_saving :
    (recursiveCertificateDataRange 1200 300 160 768 432).savingSum =
      recursiveCertificateZeroTailSaving := by
  change (recursiveCertificateDataRange 1200 300 160 768 432).savingSum = 0
  exact congrArg RecursiveCertificateData.savingSum recursive_certificate_zero_tail_block

end Landau
