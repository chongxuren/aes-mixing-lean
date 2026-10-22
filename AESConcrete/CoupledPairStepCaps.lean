import AESConcrete.CoupledPairCaps
import AESConcrete.TripleUniform

/-!
# physical aggregation for the coupled residual pair

Input multiplicity6 and four orthogonal selected output energies give
factor24. The exact certificate comparison follows that operator argument. The
eight signed inclusion-exclusion terms have already been combined before
squaring and are not assumed orthogonal.

No return or full AES10/14/16 theorem is asserted. Independent uniform
retained keys, whitening, omitted final MixColumns and the ordered-distinct
reference model remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.CoupledPairCaps (pieceSquaredBound pieceSquaredBound_nonneg)
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
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 4 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 4 p) 2 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => CoupledPairCaps.selected_piece_energy p pIn g) f

/-- Orthogonal physical output ranges give factor4, after the input factor6.
The eight signed inclusion-exclusion terms were not assumed orthogonal. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 10) f y ^ 2) ≤
      (24 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 12 10 (by decide) f]
  change (∑ p : SelectedSupport 3 4, ∑ y,
    action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 4,
        (ResidualIncidenceCoefficient.multiplicity (2 : Fin 5) 4 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 4 (by decide)]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      ring

/-- Apply the exact scalar comparison only after deriving physical factor24. -/
theorem certificate_weighted_bound :
    0 ≤ lambda * L 12 10 ∧ 24 * pieceSquaredBound ≤ (lambda * L 12 10) ^ 2 :=
  CoupledPairScalar.certificate_bound

theorem physical_12_10_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 10) f y ^ 2) ≤
      (lambda * L 12 10) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_12_10_step_cap :
    ‖kernelOperator (physicalBlock 12 10)‖ ≤ lambda * L 12 10 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_12_10_energy

theorem system_12_10_step_cap :
    ‖PhysicalProjectionSystem.system.step 12 10‖ ≤ lambda * L 12 10 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_12_10_step_cap

def weightedPair (i j : Fin 14) : Prop := i = 12 ∧ j = 10

instance (i j : Fin 14) : Decidable (weightedPair i j) := by
  unfold weightedPair
  infer_instance

def certifiedPair (i j : Fin 14) : Prop :=
  TripleUniformStepCaps.certifiedPair i j ∨ weightedPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact TripleUniformStepCaps.physical_step_cap i j h
  · exact physical_12_10_step_cap

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem predecessor_included (i j : Fin 14)
    (h : TripleUniformStepCaps.certifiedPair i j) : certifiedPair i j := Or.inl h

theorem weightedPair_included (i j : Fin 14) (h : weightedPair i j) :
    certifiedPair i j := Or.inr h

theorem weightedPair_disjoint (i j : Fin 14) :
    ¬ (weightedPair i j ∧ TripleUniformStepCaps.certifiedPair i j) := by
  revert i j
  decide

theorem weightedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2)).card = 1 := by decide

theorem weightedPair_overlap_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2 ∧
        TripleUniformStepCaps.certifiedPair ij.1 ij.2)).card = 0 := by decide

theorem additional_weightedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => weightedPair ij.1 ij.2 ∧
        ¬ TripleUniformStepCaps.certifiedPair ij.1 ij.2)).card = 1 := by decide

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 174 := by decide

theorem activity_columns_covered (i j : Fin 14)
    (hj : ActivityCodeScalar.activityColumn j) : certifiedPair i j :=
  predecessor_included i j (TripleUniformStepCaps.activity_columns_covered i j hj)

end AESConcrete.CoupledPairStepCaps
