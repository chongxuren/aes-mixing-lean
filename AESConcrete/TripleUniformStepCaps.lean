import AESConcrete.TripleUniformCaps
import AESConcrete.DoubleUniform

/-!
# Physical aggregation and the weighted-source step cap

One input multiplicity4 and four orthogonal selected output energies give the
physical factor16. The exact certificate comparison is subsequent to the
operator proof. Finite inventory counting is a separate final section. No new
return or complete AES10/14/16 theorem is asserted. Constructive mathematics
only. The fixed independent-retained-key model remains unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.TripleUniformCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Charge the actual signed input-support multiplicity once. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity (1 : Fin 5) 4 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 4 p) 1 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => TripleUniformCaps.selected_piece_energy p pIn g) f

/-- Orthogonal physical output ranges give factor4, after the input factor4.
The fourteen signed inclusion-exclusion terms were not assumed orthogonal. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 7) f y ^ 2) ≤
      (16 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 12 7 (by decide) f]
  change (∑ p : SelectedSupport 3 4, ∑ y,
    action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 4,
        (ResidualIncidenceCoefficient.multiplicity (1 : Fin 5) 4 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 4 (by decide)]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      ring

/-- Apply the exact scalar comparison only after deriving physical factor16. -/
theorem certificate_weighted_bound :
    0 ≤ lambda * L 12 7 ∧ 16 * pieceSquaredBound ≤ (lambda * L 12 7) ^ 2 :=
  TripleUniformResponseEnergy.certificate_bound

theorem physical_12_7_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 7) f y ^ 2) ≤
      (lambda * L 12 7) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_12_7_step_cap :
    ‖kernelOperator (physicalBlock 12 7)‖ ≤ lambda * L 12 7 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_12_7_energy

theorem system_12_7_step_cap :
    ‖PhysicalProjectionSystem.system.step 12 7‖ ≤ lambda * L 12 7 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_12_7_step_cap

def weightedPair (i j : Fin 14) : Prop := i = 12 ∧ j = 7

instance (i j : Fin 14) : Decidable (weightedPair i j) := by
  unfold weightedPair
  infer_instance

def certifiedPair (i j : Fin 14) : Prop :=
  DoubleUniformStepCaps.certifiedPair i j ∨ weightedPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact DoubleUniformStepCaps.physical_step_cap i j h
  · exact physical_12_7_step_cap

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : DoubleUniformStepCaps.certifiedPair i j) : certifiedPair i j := Or.inl h

theorem weightedPair_included (i j : Fin 14) (h : weightedPair i j) :
    certifiedPair i j := Or.inr h

theorem weightedPair_disjoint (i j : Fin 14) :
    ¬ (weightedPair i j ∧ DoubleUniformStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem weightedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2)).card = 1 := by decide

theorem weightedPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2 ∧
        DoubleUniformStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_weightedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2 ∧
        ¬ DoubleUniformStepCaps.certifiedPair ij.1 ij.2)).card = 1 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 173 := by decide

theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j :=
  predecessor_included i j (DoubleUniformStepCaps.activity_columns_covered i j hj)

end AESConcrete.TripleUniformStepCaps
