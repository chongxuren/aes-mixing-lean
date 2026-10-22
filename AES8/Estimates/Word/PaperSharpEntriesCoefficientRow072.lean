import AES8.Estimates.Word.PaperSharpEntriesFWHT
namespace AES8.PaperSharpEntriesCoefficientRow072
open AES8.PaperSharpEntriesFWHT
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 80000000
theorem coefficient_row (k : Index) : transform (basisVector 72) (traceIndex (byteOf k)) = sign (byteOf k) (byteOf 72) := by
  revert k
  decide +kernel
end AES8.PaperSharpEntriesCoefficientRow072
