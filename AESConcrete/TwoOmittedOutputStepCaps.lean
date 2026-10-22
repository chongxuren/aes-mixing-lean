import AESConcrete.TwoOmittedOutputCaps
import AESConcrete.ActivityMinorCaps
import AESConcrete.PhysicalProjectionSystem

/-!
# physical and system (10,6) cap

No desired bound is a premise of the physical or system endpoint.

Twelve original signed input support pieces incur one Cauchy factor12. Six
orthogonal physical output energies then add, giving72*C. The separate scalar
certificate is used after this aggregation. Every energy endpoint quantifies
over arbitrary original f, without a source-shape premise. This individual
step proves no complete AES theorem, return, initialization, experiment
linkage, terminal conversion or TV result. Constructive fixed AES10/14/16,
independent retained keys, whitening, omitted final MixColumns, ordered-
distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.TwoOmittedOutputCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

theorem input_blockType : blockType 6 = (1, 3) := rfl

theorem output_blockType : blockType 10 = (2, 4) := rfl

theorem input_multiplicity : ResidualIncidenceCoefficient.multiplicity 1 3 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem output_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 4 = 6 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem input_card : Fintype.card (SelectedSupport 1 3) = 12 := by
  rw [selectedSupport_card 1 3 (by decide), input_multiplicity]

theorem output_card : Fintype.card (SelectedSupport 2 4) = 6 := by
  rw [selectedSupport_card 2 4 (by decide), output_multiplicity]

/-- Use the kernel-general input aggregation theorem, whose e,b are arbitrary.
The separate degree-zero-only convenience wrapper is not used. -/
theorem selected_refined_input_energy (p : SelectedSupport 2 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 2 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity 1 3 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 2 4 p) 1 3 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => TwoOmittedOutputCaps.selected_piece_energy p pIn g) f

/-- Output support orthogonality gives an energy sum, not another Cauchy factor. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 10 6) f y ^ 2) ≤
      (72 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 10 6 (by decide) f]
  change (∑ p : SelectedSupport 2 4, ∑ y,
    action (selectedWordTensor 2 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 3) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 2 4,
        (ResidualIncidenceCoefficient.multiplicity 1 3 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [output_card, input_multiplicity]
      norm_num <;> ring

theorem certificate_weighted_bound :
    0 ≤ lambda * L 10 6 ∧ 72 * pieceSquaredBound ≤ (lambda * L 10 6) ^ 2 :=
  TwoOmittedOutputScalar.certificate_bound

theorem physical_10_6_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 10 6) f y ^ 2) ≤
      (lambda * L 10 6) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_10_6_step_cap :
    ‖kernelOperator (physicalBlock 10 6)‖ ≤ lambda * L 10 6 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_10_6_energy

theorem system_10_6_step_cap :
    ‖PhysicalProjectionSystem.system.step 10 6‖ ≤ lambda * L 10 6 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_10_6_step_cap

end AESConcrete.TwoOmittedOutputStepCaps
