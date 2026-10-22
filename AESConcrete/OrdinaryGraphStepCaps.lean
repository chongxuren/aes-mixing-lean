import AESConcrete.GraphFirstStepCaps
import AESConcrete.OrdinaryGraphCaps

/-!
# Ordinary graph extension of the physical step-cap inventory

The five analytic caps overlap the predecessor exactly at `(13,11)`.
Thus four new pairs are added to the 138-pair interface, conditionally on
compilation and independent review of the new proof modules. This is a
step-cap inventory only; no return, initialization, experiment linkage, or
complete AES 10/14/16 theorem is asserted. Constructive bounds only; no
attacks, manuscript or historical edits. The fixed AES model is unchanged.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OrdinaryGraphStepCaps

set_option maxRecDepth 100000

def ordinaryPair (i j : Fin 14) : Prop :=
  i = 13 ∧ OrdinaryGraphCaps.ordinaryColumn j

instance (i j : Fin 14) : Decidable (ordinaryPair i j) := by
  unfold ordinaryPair
  infer_instance

def certifiedPair (i j : Fin 14) : Prop :=
  GraphFirstStepCaps.certifiedPair i j ∨ ordinaryPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (RefinedStepZeros.physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | ⟨rfl, h⟩
  · exact GraphFirstStepCaps.physical_step_cap i j h
  · exact OrdinaryGraphCaps.physical_thirteen_step_cap j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

/-- Exact overlap at the pair level, checked independently of all energies. -/
theorem ordinaryPair_overlap_iff (i j : Fin 14) :
    ordinaryPair i j ∧ GraphFirstStepCaps.certifiedPair i j ↔ i = 13 ∧ j = 11 := by
  revert i j
  decide

theorem ordinaryPair_new_iff (i j : Fin 14) :
    ordinaryPair i j ∧ ¬ GraphFirstStepCaps.certifiedPair i j ↔
      i = 13 ∧ (j = 4 ∨ j = 5 ∨ j = 8 ∨ j = 9) := by
  revert i j
  decide

theorem ordinaryPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ordinaryPair ij.1 ij.2)).card = 5 := by decide

theorem ordinaryPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ordinaryPair ij.1 ij.2 ∧
        GraphFirstStepCaps.certifiedPair ij.1 ij.2)).card = 1 := by decide

theorem additional_ordinaryPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ordinaryPair ij.1 ij.2 ∧
        ¬ GraphFirstStepCaps.certifiedPair ij.1 ij.2)).card = 4 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 142 := by decide

end AESConcrete.OrdinaryGraphStepCaps
