import Landau.HarmanRecursiveCertificateBlock1

namespace Landau

def recursiveCertificateBlock1Saving : Nat := 151615832402575

theorem recursive_certificate_block1_saving :
    (recursiveCertificateDataRange 1200 300 160 192 192).savingSum =
      recursiveCertificateBlock1Saving := by
  change (recursiveCertificateDataRange 1200 300 160 192 192).savingSum =
    151615832402575
  exact congrArg RecursiveCertificateData.savingSum recursive_certificate_block1

end Landau
