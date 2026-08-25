import Landau.HarmanRecursiveCertificate

namespace Landau

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_block3 :
    recursiveCertificateDataRange 1200 300 160 576 192 =
      { savingSum := 41925800002266
        tailSum := 85848544729996
        a3Sum := 427595233613160
        positive := 151 } := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_zero_tail_block :
    recursiveCertificateDataRange 1200 300 160 768 432 =
      { savingSum := 0, tailSum := 0, a3Sum := 0, positive := 0 } := by
  native_decide

end Landau
