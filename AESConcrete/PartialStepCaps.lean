import AESConcrete.DegreeResidualStep
import AESConcrete.AllActiveStep
import AESConcrete.PhysicalProjectionSystem
import AESRound.CertificateMatrixChecks

/-!
# Exact inventory of the currently established physical step caps

This interface combines the 32 inherited cross-zero blocks with the 14
source-13 caps supplied by degree damping and the all-active estimate. The predicate records sufficient
proved cases only; its complement is not a claim of failure. Return caps,
initialization, experiment linkage and the full round theorem remain open.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.PartialStepCaps
open AESMixing
open RefinedStepZeros (physicalBlock crossPair physicalBlock_cross_norm)

def certifiedPair (i j : Fin 14) : Prop :=
  crossPair i j ∨ j = 13

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | rfl
  · rw [physicalBlock_cross_norm i j h]
    exact mul_nonneg AESRound.Terminal.lambda_nonneg (AESRound.Certificate.L_nonneg i j)
  · by_cases hi : i = 3
    · subst i
      exact AllActiveStep.source_thirteen_step_cap
    · exact DegreeResidualStep.column_thirteen_step_cap i hi

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 46 := by decide

end AESConcrete.PartialStepCaps
