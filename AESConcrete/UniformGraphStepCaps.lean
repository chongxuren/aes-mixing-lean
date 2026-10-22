import AESConcrete.OrdinaryGraphStepCaps
import AESConcrete.UniformGraphCaps

/-!
# Multi-uniform graph extension of the physical step-cap inventory

This candidate composes the inherited ordinary-graph inventory with the
three multi-uniform graph caps at `(13,6)`, `(13,7)` and `(13,10)`.
The finite overlap and count proofs are separate from the analytic energy
proofs. Compilation and independent source/artifact review are required
before admitting any new pair to the accepted inventory.

Constructive bounds only; no attacks, workloads, manuscript or historical
edits. Independent uniform retained keys, whitening, omitted final
MixColumns, ordered-distinct pairs and the 10/14/16 objective remain fixed.
No return, initialization, experiment linkage or complete AES theorem is
asserted by this inventory interface.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.UniformGraphStepCaps

set_option maxRecDepth 100000

def uniformPair (i j : Fin 14) : Prop :=
  i = 13 ∧ UniformGraphScalar.uniformColumn j

instance (i j : Fin 14) : Decidable (uniformPair i j) := by
  unfold uniformPair
  infer_instance

def certifiedPair (i j : Fin 14) : Prop :=
  OrdinaryGraphStepCaps.certifiedPair i j ∨ uniformPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (RefinedStepZeros.physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | ⟨rfl, h⟩
  · exact OrdinaryGraphStepCaps.physical_step_cap i j h
  · exact UniformGraphCaps.physical_thirteen_step_cap j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : OrdinaryGraphStepCaps.certifiedPair i j) : certifiedPair i j :=
  Or.inl h

/-- None of the three candidate pairs occurs in the predecessor inventory. -/
theorem uniformPair_disjoint (i j : Fin 14) :
    ¬ (uniformPair i j ∧ OrdinaryGraphStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem uniformPair_new_iff (i j : Fin 14) :
    uniformPair i j ∧ ¬ OrdinaryGraphStepCaps.certifiedPair i j ↔
      i = 13 ∧ (j = 6 ∨ j = 7 ∨ j = 10) := by
  revert i j
  decide

theorem uniformPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => uniformPair ij.1 ij.2)).card = 3 := by decide

theorem uniformPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => uniformPair ij.1 ij.2 ∧
        OrdinaryGraphStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_uniformPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => uniformPair ij.1 ij.2 ∧
        ¬ OrdinaryGraphStepCaps.certifiedPair ij.1 ij.2)).card = 3 := by decide

/-- Candidate union count; acceptance is subject to the validation gates. -/
theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 145 := by decide

end AESConcrete.UniformGraphStepCaps
