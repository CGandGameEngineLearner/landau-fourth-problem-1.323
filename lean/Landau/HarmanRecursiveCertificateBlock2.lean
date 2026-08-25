import Landau.HarmanRecursiveCertificate

namespace Landau

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_block2 :
    recursiveCertificateDataRange 1200 300 160 384 192 =
      { savingSum := 117510700363272
        tailSum := 78568822982364
        a3Sum := 143218093005705
        positive := 192 } := by
  native_decide

end Landau
