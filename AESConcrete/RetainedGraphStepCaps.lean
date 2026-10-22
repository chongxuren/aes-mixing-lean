import AESConcrete.RetainedGraphCaps

/-!
# Three-pair extension of the accepted singleton step inventory

The actual physical/system cap proof is separate from finite inventory
counting. The proposed disjoint union has 169/196 entries and adds no return.
Candidate only until compilation, independent review and durable admission.
Constructive mathematics only; no attacks or manuscript/accepted-source edits.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and fixed 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RetainedGraphStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.RetainedGraphCaps (retainedPair)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

def certifiedPair (i j : Fin 14) : Prop :=
  SingletonResidualStepCaps.certifiedPair i j ∨ retainedPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | h
  · exact SingletonResidualStepCaps.physical_step_cap i j h
  · exact RetainedGraphCaps.physical_retained_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : SingletonResidualStepCaps.certifiedPair i j) : certifiedPair i j := Or.inl h

theorem retainedPair_included (i j : Fin 14) (h : retainedPair i j) :
    certifiedPair i j := Or.inr h

theorem retainedPair_disjoint (i j : Fin 14) :
    ¬ (retainedPair i j ∧ SingletonResidualStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem retainedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => retainedPair ij.1 ij.2)).card = 3 := by decide

theorem retainedPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => retainedPair ij.1 ij.2 ∧
        SingletonResidualStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_retainedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => retainedPair ij.1 ij.2 ∧
        ¬ SingletonResidualStepCaps.certifiedPair ij.1 ij.2)).card = 3 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 169 := by decide

theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j :=
  predecessor_included i j (SingletonResidualStepCaps.activity_columns_covered i j hj)

end AESConcrete.RetainedGraphStepCaps
