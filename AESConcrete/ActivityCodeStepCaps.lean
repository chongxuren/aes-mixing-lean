import AESConcrete.UniformGraphStepCaps
import AESConcrete.ActivityCodeCaps

/-!
# Activity-only word-code extension of the physical step-cap inventory

The analytic physical energy bound is supplied by `ActivityCodeCaps` and
its scalar comparison by `ActivityCodeScalar`. This module converts them
to physical/system norm caps and composes the four activity-only pairs
with the inherited uniform-graph inventory. Overlap and counting are finite
predicate statements, separate from every operator estimate.

This is a candidate increment until compilation and independent review.
Constructive mathematics only; no attacks, workloads, manuscript or
historical edits, goals or schedules. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct pairs and 10/14/16
remain fixed. No return, initialization, experiment linkage or complete
AES theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityCodeStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

/-- Energy conversion uses the unchanged target entries only after the
actual physical energy estimate has been obtained. -/
theorem physical_thirteen_energy (j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      (lambda * L 13 j) ^ 2 * ∑ x, f x ^ 2 :=
  (ActivityCodeCaps.physicalBlock_energy j hj f).trans
    (mul_le_mul_of_nonneg_right (ActivityCodeScalar.certificate_activity_bounds j hj).2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_thirteen_step_cap (j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) :
    ‖kernelOperator (physicalBlock 13 j)‖ ≤ lambda * L 13 j :=
  kernelOperator_norm_le _ (ActivityCodeScalar.certificate_activity_bounds j hj).1
    (physical_thirteen_energy j hj)

theorem system_thirteen_step_cap (j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) :
    ‖PhysicalProjectionSystem.system.step 13 j‖ ≤ lambda * L 13 j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_thirteen_step_cap j hj

theorem physical_thirteen_zero_step_cap :
    ‖kernelOperator (physicalBlock 13 0)‖ ≤ lambda * L 13 0 :=
  physical_thirteen_step_cap 0 (by decide)

theorem physical_thirteen_one_step_cap :
    ‖kernelOperator (physicalBlock 13 1)‖ ≤ lambda * L 13 1 :=
  physical_thirteen_step_cap 1 (by decide)

theorem physical_thirteen_two_step_cap :
    ‖kernelOperator (physicalBlock 13 2)‖ ≤ lambda * L 13 2 :=
  physical_thirteen_step_cap 2 (by decide)

theorem physical_thirteen_three_step_cap :
    ‖kernelOperator (physicalBlock 13 3)‖ ≤ lambda * L 13 3 :=
  physical_thirteen_step_cap 3 (by decide)

theorem system_thirteen_zero_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 0‖ ≤ lambda * L 13 0 :=
  system_thirteen_step_cap 0 (by decide)

theorem system_thirteen_one_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 1‖ ≤ lambda * L 13 1 :=
  system_thirteen_step_cap 1 (by decide)

theorem system_thirteen_two_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 2‖ ≤ lambda * L 13 2 :=
  system_thirteen_step_cap 2 (by decide)

theorem system_thirteen_three_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 3‖ ≤ lambda * L 13 3 :=
  system_thirteen_step_cap 3 (by decide)

def activityPair (i j : Fin 14) : Prop :=
  i = 13 ∧ ActivityCodeScalar.activityColumn j

instance (i j : Fin 14) : Decidable (activityPair i j) := by
  unfold activityPair
  infer_instance

def certifiedPair (i j : Fin 14) : Prop :=
  UniformGraphStepCaps.certifiedPair i j ∨ activityPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | ⟨rfl, h⟩
  · exact UniformGraphStepCaps.physical_step_cap i j h
  · exact physical_thirteen_step_cap j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : UniformGraphStepCaps.certifiedPair i j) : certifiedPair i j :=
  Or.inl h

/-- All four activity-only pairs are absent from the predecessor. -/
theorem activityPair_disjoint (i j : Fin 14) :
    ¬ (activityPair i j ∧ UniformGraphStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem activityPair_new_iff (i j : Fin 14) :
    activityPair i j ∧ ¬ UniformGraphStepCaps.certifiedPair i j ↔
      i = 13 ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) := by
  revert i j
  decide

theorem activityPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => activityPair ij.1 ij.2)).card = 4 := by decide

theorem activityPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => activityPair ij.1 ij.2 ∧
        UniformGraphStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_activityPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => activityPair ij.1 ij.2 ∧
        ¬ UniformGraphStepCaps.certifiedPair ij.1 ij.2)).card = 4 := by decide

/-- Candidate union count; acceptance requires the validation gates. -/
theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 149 := by decide

/-- The four new pairs complete the actual four-residual output row. -/
theorem row_thirteen_covered (j : Fin 14) : certifiedPair 13 j := by
  revert j
  decide

theorem physical_row_thirteen_step_cap (j : Fin 14) :
    ‖kernelOperator (physicalBlock 13 j)‖ ≤ lambda * L 13 j :=
  physical_step_cap 13 j (row_thirteen_covered j)

theorem system_row_thirteen_step_cap (j : Fin 14) :
    ‖PhysicalProjectionSystem.system.step 13 j‖ ≤ lambda * L 13 j :=
  system_step_cap 13 j (row_thirteen_covered j)

end AESConcrete.ActivityCodeStepCaps
