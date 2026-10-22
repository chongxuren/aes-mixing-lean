import AES8.Estimates.Word.PaperSharpEntriesFWHT
namespace AES8.PaperSharpEntriesCoefficientRow254
open AES8.PaperSharpEntriesFWHT
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 80000000
theorem coefficient_row (k : Index) : transform (basisVector 254) (traceIndex (byteOf k)) = sign (byteOf k) (byteOf 254) := by
  revert k
  decide +kernel
end AES8.PaperSharpEntriesCoefficientRow254
