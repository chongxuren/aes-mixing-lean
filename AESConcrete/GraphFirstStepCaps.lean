import AESConcrete.DirectIncidenceStepCaps
import AESConcrete.MDSGraphFirstCap
import AESConcrete.NonzeroUniformGraphCap

/-! Candidate union of the accepted136-cap interface and the MDS graph
caps (13,11) and (13,12). The count concerns step caps only. No full AES theorem
is asserted. Constructive mathematics only; no attacks or manuscript edits. -/

set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators
namespace AESConcrete.GraphFirstStepCaps

def certifiedPair (i j : Fin 14) : Prop :=
  DirectIncidenceStepCaps.certifiedPair i j ∨ (i = 13 ∧ (j = 11 ∨ j = 12))

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (RefinedStepZeros.physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | ⟨rfl, h⟩
  · exact DirectIncidenceStepCaps.physical_step_cap i j h
  · rcases h with rfl | rfl
    · exact MDSGraphFirstCap.physical_thirteen_eleven_step_cap
    · exact NonzeroUniformGraphCap.physical_thirteen_twelve_step_cap

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem additional_pair_not_predecessor :
    ¬ DirectIncidenceStepCaps.certifiedPair 13 11 := by decide

theorem second_additional_pair_not_predecessor :
    ¬ DirectIncidenceStepCaps.certifiedPair 13 12 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 138 := by decide

end AESConcrete.GraphFirstStepCaps
