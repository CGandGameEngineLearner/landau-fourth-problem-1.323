import Landau.HarmanRecursiveCertificateBlock2

namespace Landau

def recursiveCertificateBlock2Saving : Nat := 117510700363272

theorem recursive_certificate_block2_saving :
    (recursiveCertificateDataRange 1200 300 160 384 192).savingSum =
      recursiveCertificateBlock2Saving := by
  change (recursiveCertificateDataRange 1200 300 160 384 192).savingSum =
    117510700363272
  exact congrArg RecursiveCertificateData.savingSum recursive_certificate_block2

end Landau
