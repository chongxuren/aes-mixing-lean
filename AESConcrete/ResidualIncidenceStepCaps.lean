import AESConcrete.ActivityFullStepCaps
import AESConcrete.ResidualIncidenceStep

/-! Separate candidate union of the accepted 85-case interface and forty-two
fixed-activity incidence caps. Compilation/review/acceptance are separate.
Constructive mathematics only; no attacks or manuscript/historical edits.
The model and 10/14/16 target are unchanged; the full theorem remains open. -/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ResidualIncidenceStepCaps
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock blockType)

def certifiedPair (i j : Fin 14) : Prop :=
  ActivityFullStepCaps.certifiedPair i j ∨ ResidualIncidenceStep.incidencePair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | h
  · exact ActivityFullStepCaps.physical_step_cap i j h
  · exact ResidualIncidenceStep.physical_incidence_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem incidencePair_disjoint : ∀ i j : Fin 14,
    ResidualIncidenceStep.incidencePair i j → ¬ ActivityFullStepCaps.certifiedPair i j := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 127 := by decide

theorem additional_incidencePair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => ResidualIncidenceStep.incidencePair ij.1 ij.2 ∧
        ¬ ActivityFullStepCaps.certifiedPair ij.1 ij.2)).card = 42 := by decide

/-- Every first-eight-row cell is covered by one of the distinct arguments. -/
theorem low_output_covered : ∀ i j : Fin 14,
    (blockType i).1.val ≤ 1 → certifiedPair i j := by decide

end AESConcrete.ResidualIncidenceStepCaps
