import AESConcrete.ActivityRankOneStep

/-!
# Partial step caps extended by six activity rank-one blocks

This separate candidate combines the accepted 69-case branch interface with
the six activity-only raw-zero cases. Return caps, initialization, retained-key
experiment identification and the full AES 10/14/16 theorem remain open.
Constructive mathematics only; no attacks or manuscript/historical edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityRankStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)

def certifiedPair (i j : Fin 14) : Prop :=
  BranchStepCaps.certifiedPair i j ∨ ActivityRankOneStep.rankPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | h
  · exact BranchStepCaps.physical_step_cap i j h
  · exact ActivityRankOneStep.physical_rank_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 75 := by decide

theorem additional_rankPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ActivityRankOneStep.rankPair ij.1 ij.2 ∧
        ¬ BranchStepCaps.certifiedPair ij.1 ij.2)).card = 6 := by decide

end AESConcrete.ActivityRankStepCaps
