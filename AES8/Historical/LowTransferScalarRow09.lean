/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.LegacyTransfer
import AESRound.Terminal
import AESRound.CertificateData

/-! Independent scalar row 9 of the low-coefficient comparison.
Only the fixed rational comparison is split for parallel compilation.
The low-basis sum is proved before concrete case splitting, so simplification
does not turn an unresolved finite cast equality into a filtered cardinality.
No operator cap, changed coefficient, attack, or manuscript edit occurs here. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.LowTransferScalarParallel

-- This generic identity removes the eleven-term lowSum before row arithmetic.
-- Prove cast injectivity through values; do not ask simp to unfold finite
-- enumeration/cardinality on the concrete AES-imported environment.
private theorem lowSum_low_basis (k : Fin 11) :
    lowSum (TransferAssembly.basis (Fin.castAdd 3 k)) = 1 := by
  change (∑ j : Fin 11, if (Fin.castAdd 3 j : Fin 14) = Fin.castAdd 3 k
    then (1 : ℝ) else 0) = 1
  have he (j : Fin 11) :
      (Fin.castAdd 3 j : Fin 14) = Fin.castAdd 3 k ↔ j = k := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun x : Fin 14 => x.val) h)
    · rintro rfl
      rfl
  simp only [he]
  simp

/-- The same fixed scalar comparison as LowTransfer, for output row 9. -/
theorem row09_coefficient_le (k : Fin 11) :
    AESRound.Terminal.lambda * AESRound.Certificate.L (9 : Fin 14) (Fin.castAdd 3 k) ≤
      TransferAssembly.physicalCoeff 1 (9 : Fin 14) (Fin.castAdd 3 k)
        (TransferAssembly.lowCoeff (9 : Fin 14) k) := by
  change AESRound.Terminal.lambda *
      AESRound.Certificate.L (9 : Fin 14) (Fin.castAdd 3 k) ≤
    omega41 ^ 1 * d (9 : Fin 14) / d (Fin.castAdd 3 k) *
      (L0 (TransferAssembly.basis (Fin.castAdd 3 k)) (9 : Fin 14) +
        lowSum (TransferAssembly.basis (Fin.castAdd 3 k)) / 4096)
  rw [lowSum_low_basis]
  fin_cases k <;>
    simp only [L0, d, vec14_apply, TransferAssembly.basis,
      Fin.ext_iff, Fin.castAdd, Fin.castLE, Fin.val_mk] <;>
    norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L, omega41,
      Fin.ext_iff, Fin.castAdd, Fin.castLE, Fin.val_mk]

end AES8.LowTransferScalarParallel

