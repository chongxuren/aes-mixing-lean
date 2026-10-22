import AESConcrete.ActivityRankStepCaps
import AESConcrete.ActivityFullStep

/-! Separate extension of the frozen 75-cap interface by all sixteen
activity-only pairs, giving ten additional caps and 85 total. Return caps,
initialization, experiment linkage and the full 10/14/16 target remain open.
Constructive mathematics only; no attacks or manuscript/historical edits. -/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityFullStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)

def certifiedPair (i j : Fin 14) : Prop :=
  ActivityRankStepCaps.certifiedPair i j ∨ ActivityFullStep.activityPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | h
  · exact ActivityRankStepCaps.physical_step_cap i j h
  · exact ActivityFullStep.physical_activity_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 85 := by decide

theorem additional_activityPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ActivityFullStep.activityPair ij.1 ij.2 ∧
        ¬ ActivityRankStepCaps.certifiedPair ij.1 ij.2)).card = 10 := by decide

end AESConcrete.ActivityFullStepCaps
