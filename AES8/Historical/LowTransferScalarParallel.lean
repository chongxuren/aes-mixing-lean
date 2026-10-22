/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.LowTransferScalarRow00
import AES8.Historical.LowTransferScalarRow01
import AES8.Historical.LowTransferScalarRow02
import AES8.Historical.LowTransferScalarRow03
import AES8.Historical.LowTransferScalarRow04
import AES8.Historical.LowTransferScalarRow05
import AES8.Historical.LowTransferScalarRow06
import AES8.Historical.LowTransferScalarRow07
import AES8.Historical.LowTransferScalarRow08
import AES8.Historical.LowTransferScalarRow09
import AES8.Historical.LowTransferScalarRow10
import AES8.Historical.LowTransferScalarRow11
import AES8.Historical.LowTransferScalarRow12
import AES8.Historical.LowTransferScalarRow13

/-! Scalar-only dispatcher for fourteen independently compiled low-cap rows.
This module imports neither LowTransfer nor AllStepCaps. -/

set_option autoImplicit false
noncomputable section

namespace AES8.LowTransferScalarParallel

/-- Exact replacement API for the scalar lemma in LowTransfer. -/
theorem legacy_low_coefficient_le (i : Fin 14) (k : Fin 11) :
    AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.castAdd 3 k) ≤
      TransferAssembly.physicalCoeff 1 i (Fin.castAdd 3 k)
        (TransferAssembly.lowCoeff i k) := by
  fin_cases i
  · exact row00_coefficient_le k
  · exact row01_coefficient_le k
  · exact row02_coefficient_le k
  · exact row03_coefficient_le k
  · exact row04_coefficient_le k
  · exact row05_coefficient_le k
  · exact row06_coefficient_le k
  · exact row07_coefficient_le k
  · exact row08_coefficient_le k
  · exact row09_coefficient_le k
  · exact row10_coefficient_le k
  · exact row11_coefficient_le k
  · exact row12_coefficient_le k
  · exact row13_coefficient_le k

end AES8.LowTransferScalarParallel

