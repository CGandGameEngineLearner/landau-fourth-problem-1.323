import Landau.HarmanRecursiveCertificate

namespace Landau

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_block1 :
    recursiveCertificateDataRange 1200 300 160 192 192 =
      { savingSum := 151615832402575
        tailSum := 66017311073159
        a3Sum := 51568363842395
        positive := 192 } := by
  native_decide

end Landau
