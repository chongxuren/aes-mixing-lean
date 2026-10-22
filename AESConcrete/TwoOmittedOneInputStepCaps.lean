import AESConcrete.TwoOmittedOneInputCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# arbitrary-input physical and system cap for (10,12)

Four original input support pieces incur ONE Cauchy factor4. Six orthogonal
output energies add, giving24*C. Neither endpoint assumes a desired-bound
premise or a source shape. This individual cell gives no complete AES theorem
or TV conclusion. The repaired generic pushforward helper and all modules
remain dependencies. Constructive AES10/14/16, independent uniform retained
keys, whitening, omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.TwoOmittedOneInputCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

theorem input_blockType : blockType 12 = (3, 4) := rfl
theorem output_blockType : blockType 10 = (2, 4) := rfl

theorem input_multiplicity : ResidualIncidenceCoefficient.multiplicity 3 4 = 4 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem output_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 4 = 6 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem input_card : Fintype.card (SelectedSupport 3 4) = 4 := by
  rw [selectedSupport_card 3 4 (by decide), input_multiplicity]

theorem output_card : Fintype.card (SelectedSupport 2 4) = 6 := by
  rw [selectedSupport_card 2 4 (by decide), output_multiplicity]

/-- Use the kernel-general arbitrary-e,b aggregation interface. -/
theorem selected_refined_input_energy (p : SelectedSupport 2 4) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 3 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 3 4 : ℝ) * pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 4 p) 3 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => TwoOmittedOneInputCaps.selected_piece_energy p pIn g) f

/-- Output orthogonality gives an energy sum; no second output Cauchy factor. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 10 12) f y ^ 2) ≤
      (24 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 10 12 (by decide) f]
  change (∑ p : SelectedSupport 2 4, ∑ y, action (selectedWordTensor 2 4 p)
    (fun x => action (refinedKernel (0 : AES.Word) 3 4) f (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 2 4,
        (ResidualIncidenceCoefficient.multiplicity 3 4 : ℝ) * pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [output_card, input_multiplicity]
      norm_num <;> ring

theorem certificate_weighted_bound :
    0 ≤ lambda * L 10 12 ∧ 24 * pieceSquaredBound ≤ (lambda * L 10 12) ^ 2 :=
  TwoOmittedOneInputScalar.certificate_bound

theorem physical_10_12_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 10 12) f y ^ 2) ≤
      (lambda * L 10 12) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_10_12_step_cap :
    ‖kernelOperator (physicalBlock 10 12)‖ ≤ lambda * L 10 12 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_10_12_energy

theorem system_10_12_step_cap :
    ‖PhysicalProjectionSystem.system.step 10 12‖ ≤ lambda * L 10 12 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_10_12_step_cap

end AESConcrete.TwoOmittedOneInputStepCaps
