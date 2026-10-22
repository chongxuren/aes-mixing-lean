import AESConcrete.ResidualIncidenceStepCaps
import AESConcrete.DirectIncidenceStep

/-!
Separate union: the 127-case interface plus nine direct restricted-
incidence caps. Return caps, initialization, experiment linkage and the full 10/14/16 theorem are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DirectIncidenceStepCaps
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)

def certifiedPair (i j : Fin 14) : Prop :=
  ResidualIncidenceStepCaps.certifiedPair i j ∨ DirectIncidenceStep.directPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | h
  · exact ResidualIncidenceStepCaps.physical_step_cap i j h
  · exact DirectIncidenceStep.physical_direct_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem directPair_disjoint : ∀ i j : Fin 14,
    DirectIncidenceStep.directPair i j → ¬ ResidualIncidenceStepCaps.certifiedPair i j := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 136 := by decide

theorem additional_directPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => DirectIncidenceStep.directPair ij.1 ij.2 ∧
        ¬ ResidualIncidenceStepCaps.certifiedPair ij.1 ij.2)).card = 9 := by decide

end AESConcrete.DirectIncidenceStepCaps
