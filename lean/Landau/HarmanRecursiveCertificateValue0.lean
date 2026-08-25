import Landau.HarmanRecursiveCertificateBlock0

namespace Landau

def recursiveCertificateBlock0Saving : Nat := 154113574025565

theorem recursive_certificate_block0_saving :
    (recursiveCertificateDataRange 1200 300 160 0 192).savingSum =
      recursiveCertificateBlock0Saving := by
  change (recursiveCertificateDataRange 1200 300 160 0 192).savingSum =
    154113574025565
  exact congrArg RecursiveCertificateData.savingSum recursive_certificate_block0

end Landau
