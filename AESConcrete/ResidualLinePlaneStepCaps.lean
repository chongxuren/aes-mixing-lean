import AESConcrete.CoupledPair
import AESConcrete.TwoResidualLineStepCaps
import AESConcrete.ThreeResidualLineStepCaps
import AESConcrete.ThreeResidualPlaneStepCaps

/-!
# Union of the two actual-line caps and actual-plane cap

This module adds the three distinct individual cells (8,11), (11,8), (11,11)
to the CoupledPair step predicate. It imports their exact independently
derived cap interfaces; it does not repeat or strengthen their geometry,
transport or energy proofs. This union alone does not establish a new return
or complete AES theorem.

The predicate, cap dispatch and finite coverage counts have separate roles.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section

namespace AESConcrete.ResidualLinePlaneStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

/-- Exactly the three separately derived cells; no return is added. -/
def additionalPair (i j : Fin 14) : Prop :=
  (i = 8 ∧ j = 11) ∨ (i = 11 ∧ j = 8) ∨ (i = 11 ∧ j = 11)

instance (i j : Fin 14) : Decidable (additionalPair i j) := by
  unfold additionalPair
  infer_instance

/--
The predecessor is the CoupledPair step predicate.
-/
def certifiedPair (i j : Fin 14) : Prop :=
  CoupledPairStepCaps.certifiedPair i j ∨ additionalPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

/-- Dispatch only to the inherited cap or one of the three individual caps. -/
theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with hpre | hnew
  · exact CoupledPairStepCaps.physical_step_cap i j hpre
  · rcases hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact TwoResidualLineStepCaps.physical_8_11_step_cap
    · exact ThreeResidualLineStepCaps.physical_11_8_step_cap
    · exact ThreeResidualPlaneStepCaps.physical_11_11_step_cap

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : CoupledPairStepCaps.certifiedPair i j) : certifiedPair i j := Or.inl h

theorem additionalPair_included (i j : Fin 14) (h : additionalPair i j) :
    certifiedPair i j := Or.inr h

theorem cell_8_11_included : certifiedPair 8 11 :=
  additionalPair_included 8 11 (Or.inl ⟨rfl, rfl⟩)

theorem cell_11_8_included : certifiedPair 11 8 :=
  additionalPair_included 11 8 (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem cell_11_11_included : certifiedPair 11 11 :=
  additionalPair_included 11 11 (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- The three displayed ordered cells are pairwise distinct. -/
theorem additional_cells_distinct :
    ((8 : Fin 14), (11 : Fin 14)) ≠ ((11 : Fin 14), (8 : Fin 14)) ∧
    ((8 : Fin 14), (11 : Fin 14)) ≠ ((11 : Fin 14), (11 : Fin 14)) ∧
    ((11 : Fin 14), (8 : Fin 14)) ≠ ((11 : Fin 14), (11 : Fin 14)) := by decide

theorem additionalPair_disjoint (i j : Fin 14) :
    ¬ (additionalPair i j ∧ CoupledPairStepCaps.certifiedPair i j) := by
  revert i j
  decide

/-- This count is inherited from the prospective predecessor only. -/
theorem predecessor_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => CoupledPairStepCaps.certifiedPair ij.1 ij.2)).card = 174 :=
  CoupledPairStepCaps.certifiedPair_count

theorem additionalPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => additionalPair ij.1 ij.2)).card = 3 := by decide

theorem additionalPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => additionalPair ij.1 ij.2 ∧
        CoupledPairStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additionalPair_new_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => additionalPair ij.1 ij.2 ∧
        ¬ CoupledPairStepCaps.certifiedPair ij.1 ij.2)).card = 3 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 177 := by decide

/-- The prospective union has exactly predecessor174 plus three new cells. -/
theorem certifiedPair_count_split :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card =
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => CoupledPairStepCaps.certifiedPair ij.1 ij.2)).card +
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => additionalPair ij.1 ij.2)).card := by
  rw [certifiedPair_count, predecessor_count, additionalPair_count]

theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j :=
  predecessor_included i j (CoupledPairStepCaps.activity_columns_covered i j hj)

end AESConcrete.ResidualLinePlaneStepCaps
