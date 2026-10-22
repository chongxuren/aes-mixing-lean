import AESConcrete.OmittedUniformTwoInputPairCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# (9,10) physical aggregation

The pair-source, raw-response, event-bound and omitted-output-split interfaces
are used at their exact types. The original arbitrary signed JOINT residual-
pair amplitude is preserved, including its value at zero. There are two
original input uniforms. Six input support pieces incur one Cauchy factor6.
Twelve orthogonal output energies then give factor72, before the unchanged
scalar certificate is used. This individual cap does not establish returns or
the full AES theorem. Constructive fixed AES10/14/16, independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct
reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoInputPairStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.OmittedUniformTwoInputPairCaps (pieceSquaredBound pieceSquaredBound_nonneg)
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

theorem output_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 3 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

/-- Charge the original six signed input support pieces exactly once. -/
theorem selected_refined_input_energy (p : SelectedSupport 2 3)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 2 4 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 3 p) 2 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => OmittedUniformTwoInputPairCaps.selected_piece_energy p pIn g) f

/-- The output sum is orthogonal energy, with no second Cauchy factor. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 10) f y ^ 2) ≤
      (72 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 9 10 (by decide) f]
  change (∑ p : SelectedSupport 2 3, ∑ y,
    action (selectedWordTensor 2 3 p)
      (fun x => action (refinedKernel (0 : AES.Word) 2 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 2 3,
        (ResidualIncidenceCoefficient.multiplicity 2 4 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 2 3 (by decide), output_multiplicity, input_multiplicity]
      norm_num <;> ring

theorem certificate_weighted_bound :
    0 ≤ lambda * L 9 10 ∧ 72 * pieceSquaredBound ≤ (lambda * L 9 10) ^ 2 :=
  OmittedUniformTwoInputPairScalar.certificate_bound

theorem physical_9_10_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 9 10) f y ^ 2) ≤
      (lambda * L 9 10) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_9_10_step_cap :
    ‖kernelOperator (physicalBlock 9 10)‖ ≤ lambda * L 9 10 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_9_10_energy

theorem system_9_10_step_cap :
    ‖PhysicalProjectionSystem.system.step 9 10‖ ≤ lambda * L 9 10 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_9_10_step_cap

end AESConcrete.OmittedUniformTwoInputPairStepCaps
