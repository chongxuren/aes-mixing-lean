import AESConcrete.ActivityMinorCaps

/-!
# Physical and system caps from activity-minor aggregation

Candidate extension: acceptance requires complete compilation and independent
review. The scalar comparison is applied only after the actual physical energy
estimate. Inventory counting is separate from the operator proof.
Constructive mathematics only; no attacks or manuscript changes. Independent
uniform retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target are unchanged. Remaining returns and the
full experiment/initialization/terminal/TV bridges are not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinorBoundsStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

theorem physical_minor_energy (i j : Fin 14)
    (h : ActivityMinorScalar.minorPair i j) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (lambda * L i j) ^ 2 * ∑ x, f x ^ 2 :=
  (ActivityMinorCaps.physicalBlock_energy i j h f).trans
    (mul_le_mul_of_nonneg_right (ActivityMinorScalar.certificate_minor_bounds i j h).2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_minor_step_cap (i j : Fin 14)
    (h : ActivityMinorScalar.minorPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j :=
  kernelOperator_norm_le _ (ActivityMinorScalar.certificate_minor_bounds i j h).1
    (physical_minor_energy i j h)

theorem system_minor_step_cap (i j : Fin 14)
    (h : ActivityMinorScalar.minorPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_minor_step_cap i j h

def certifiedPair (i j : Fin 14) : Prop :=
  ActivityCodeStepCaps.certifiedPair i j ∨ ActivityMinorScalar.minorPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | h
  · exact ActivityCodeStepCaps.physical_step_cap i j h
  · exact physical_minor_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : ActivityCodeStepCaps.certifiedPair i j) : certifiedPair i j := Or.inl h

theorem minorPair_disjoint (i j : Fin 14) :
    ¬ (ActivityMinorScalar.minorPair i j ∧ ActivityCodeStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem minorPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ActivityMinorScalar.minorPair ij.1 ij.2)).card = 16 := by
  decide

theorem minorPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ActivityMinorScalar.minorPair ij.1 ij.2 ∧
        ActivityCodeStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_minorPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ActivityMinorScalar.minorPair ij.1 ij.2 ∧
        ¬ ActivityCodeStepCaps.certifiedPair ij.1 ij.2)).card = 16 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 165 := by decide

/-- All four zero-residual-degree input columns are covered by the union. -/
theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j := by
  revert i j
  decide

theorem physical_activity_columns_step_cap (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j :=
  physical_step_cap i j (activity_columns_covered i j hj)

theorem system_activity_columns_step_cap (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j :=
  system_step_cap i j (activity_columns_covered i j hj)

end AESConcrete.ActivityMinorBoundsStepCaps
