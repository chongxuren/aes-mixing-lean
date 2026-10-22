import AESConcrete.SingletonResidualCaps

/-! Candidate extension by the physical singleton-input cap (12,4).
Finite inventory is distinct from operator evidence. No new return or complete
AES theorem is asserted; compilation and independent review remain required.
Constructive only; no attacks, manuscript or accepted-source edits. -/

noncomputable section
open scoped BigOperators

namespace AESConcrete.SingletonResidualStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

def certifiedPair (i j : Fin 14) : Prop :=
  ActivityMinorBoundsStepCaps.certifiedPair i j ∨ (i = 12 ∧ j = 4)

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact ActivityMinorBoundsStepCaps.physical_step_cap i j h
  · exact SingletonResidualCaps.physical_singleton_step_cap

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : ActivityMinorBoundsStepCaps.certifiedPair i j) : certifiedPair i j :=
  Or.inl h

theorem singleton_pair_new :
    ¬ ActivityMinorBoundsStepCaps.certifiedPair 12 4 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 166 := by decide

theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j :=
  predecessor_included i j (ActivityMinorBoundsStepCaps.activity_columns_covered i j hj)

end AESConcrete.SingletonResidualStepCaps
