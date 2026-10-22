/- Module role: Concrete transfer caps and their comparison to the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.LegacyTransfer
import AESConcrete.AllStepCaps
import AES8.Historical.LowTransferScalarParallel

/-!
# Reuse of the admitted physical low-input step caps

The predecessor's all-step dispatcher bounds the exact centered physical
sandwich used by `LegacyTransfer`.  The finite coefficient comparison uses
the enlarged low matrix in `Data.lean`, obtained from the exact
`old_low` trajectory.
The nine enlarged entries include the existing common `1/4096` contribution.

The endpoint is the low field of `TransferAssembly.PhysicalCaps`, for arbitrary
joint real input functions.  Return caps and the first high remainder remain
separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.constructorNameAsVariable false

noncomputable section

namespace AES8.LowTransfer
open AESMixing AESMixing.AES AESConcrete

/-- Exact equality of the local and admitted predecessor centered block formulas. -/
theorem physicalBlock_eq_legacy (i j : Fin 14) :
    LegacyTransfer.physicalBlock i j = RefinedStepZeros.physicalBlock i j := rfl

/-- Exact equality of the Euclidean operators, without a change of measure. -/
theorem euclideanBlock_eq_legacy (i j : Fin 14) :
    LegacyTransfer.euclideanBlock i j =
      kernelOperator (RefinedStepZeros.physicalBlock i j) := by
  unfold LegacyTransfer.euclideanBlock
  rw [physicalBlock_eq_legacy]

-- Dependency: these 154 rational inequalities require the nine enlarged L0
-- coefficients in Data.lean.  Do not restore the earlier
-- low table without revisiting this lemma and the scalar recurrence checks.
/-- The new physical low coefficients dominate every admitted old low-column cap. -/
theorem legacy_low_coefficient_le (i : Fin 14) (k : Fin 11) :
    AESRound.Terminal.lambda * AESRound.Certificate.L i (Fin.castAdd 3 k) ≤
      TransferAssembly.physicalCoeff 1 i (Fin.castAdd 3 k)
        (TransferAssembly.lowCoeff i k) :=
  LowTransferScalarParallel.legacy_low_coefficient_le i k

/-- Concrete low-column operator cap from the admitted all-step theorem. -/
theorem low_operator_cap (i : Fin 14) (k : Fin 11) :
    ‖LegacyTransfer.euclideanBlock i (Fin.castAdd 3 k)‖ ≤
      TransferAssembly.physicalCoeff 1 i (Fin.castAdd 3 k)
        (TransferAssembly.lowCoeff i k) := by
  rw [euclideanBlock_eq_legacy]
  exact (AllStepCaps.physical_step_cap i (Fin.castAdd 3 k)).trans
    (legacy_low_coefficient_le i k)

/-- Unconditional low field of `TransferAssembly.PhysicalCaps` after compilation.
This theorem supplies neither of that structure's two remaining analytic fields. -/
theorem low_profile_cap (f : WordState → ℝ) (i : Fin 14) (k : Fin 11) :
    SupportProfile.profile
        (TransferAssembly.centeredStep (SupportProfile.component f (Fin.castAdd 3 k))) i ≤
      TransferAssembly.physicalCoeff 1 i (Fin.castAdd 3 k)
          (TransferAssembly.lowCoeff i k) *
        SupportProfile.profile f (Fin.castAdd 3 k) :=
  LegacyTransfer.low_profile_caps_of_operator_caps low_operator_cap f i k

end AES8.LowTransfer
