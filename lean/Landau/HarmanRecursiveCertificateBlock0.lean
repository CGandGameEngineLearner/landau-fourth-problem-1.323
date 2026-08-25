import Landau.HarmanRecursiveCertificate

namespace Landau

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_block0 :
    recursiveCertificateDataRange 1200 300 160 0 192 =
      { savingSum := 154113574025565
        tailSum := 33521124690535
        a3Sum := 17837077097522
        positive := 192 } := by
  native_decide

end Landau
