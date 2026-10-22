import AESConcrete.TwoUniformThreeOutputCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# Physical (11,10) cap from two original input uniform weights

Six signed input support pieces incur one Cauchy multiplicity. Four orthogonal
output energies then give physical factor24. The exact certificate comparison
follows this aggregation. This individual operator cap supplies no return,
initialization, experiment or TV theorem. Constructive independent-retained-
key AES10/14/16 with whitening, omitted final MixColumns and ordered-distinct
reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoUniformThreeOutputStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.TwoUniformThreeOutputCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

theorem input_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 4 = 6 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- Charge the actual six input support pieces once. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 2 4 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 3 p) 2 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => TwoUniformThreeOutputCaps.selected_piece_energy p pIn g) f

/-- Four orthogonal output energies give total physical factor24. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 10) f y ^ 2) ≤
      (24 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 11 10 (by decide) f]
  change (∑ p : SelectedSupport 3 3, ∑ y,
    action (selectedWordTensor 3 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 3,
        (ResidualIncidenceCoefficient.multiplicity 2 4 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 3 (by decide), input_multiplicity]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose] <;> ring

theorem certificate_weighted_bound :
    0 ≤ lambda * L 11 10 ∧ 24 * pieceSquaredBound ≤ (lambda * L 11 10) ^ 2 :=
  TwoUniformThreeOutputScalar.certificate_bound

theorem physical_11_10_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 11 10) f y ^ 2) ≤
      (lambda * L 11 10) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_11_10_step_cap :
    ‖kernelOperator (physicalBlock 11 10)‖ ≤ lambda * L 11 10 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_11_10_energy

theorem system_11_10_step_cap :
    ‖PhysicalProjectionSystem.system.step 11 10‖ ≤ lambda * L 11 10 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_11_10_step_cap

end AESConcrete.TwoUniformThreeOutputStepCaps
