import AESConcrete.TwoOutputThreeUniformScalar
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Individual physical/system cap (8,7)

Four actual input support pieces incur one Cauchy factor. Six orthogonal
output support energies are then summed, giving factor24. Scalar comparison
follows this physical aggregation.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference. No return cap or
complete AES theorem is asserted.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOutputThreeUniformStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.TwoOutputThreeUniformCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESConcrete.TwoOutputThreeUniformScalar (certificate_8_7_bound)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

theorem selected_refined_input_energy (p : SelectedSupport 2 2) (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 2 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 1 4 : ℝ) * pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 2 p) 1 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => TwoOutputThreeUniformCaps.selected_piece_energy p pIn g) f

theorem input_multiplicity : ResidualIncidenceCoefficient.multiplicity 1 4 = 4 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem physical_code_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 7) f y ^ 2) ≤ (24 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 8 7 (by decide) f]
  change (∑ p : SelectedSupport 2 2, ∑ y, action (selectedWordTensor 2 2 p)
    (fun x => action (refinedKernel (0 : AES.Word) 1 4) f (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 2 2,
        (ResidualIncidenceCoefficient.multiplicity 1 4 : ℝ) * pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 2 2 (by decide), input_multiplicity]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose] <;> ring

theorem physical_8_7_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 8 7) f y ^ 2) ≤ (lambda * L 8 7) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_code_energy f).trans (mul_le_mul_of_nonneg_right certificate_8_7_bound.2.le
    (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_8_7_step_cap : ‖kernelOperator (physicalBlock 8 7)‖ ≤ lambda * L 8 7 :=
  kernelOperator_norm_le _ certificate_8_7_bound.1 physical_8_7_energy

theorem system_8_7_step_cap : ‖PhysicalProjectionSystem.system.step 8 7‖ ≤ lambda * L 8 7 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_8_7_step_cap

end AESConcrete.TwoOutputThreeUniformStepCaps
