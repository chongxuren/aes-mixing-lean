import AESConcrete.CoupledTripleCaps
import AESConcrete.CoupledPair

/-!
# Physical support aggregation for the joint residual triple

The support indices are `(12,12)`. Four signed input pieces and four
orthogonal selected output energies give factor16. The four signed exclusion
responses have already been combined before squaring.

Constructive independent uniform retained keys, whitening, omitted final
MixColumns and ordered-distinct reference pairs.

This individual physical/system bound does not establish the full AES10/14/16
theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleStepCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.CoupledTripleCaps (pieceSquaredBound pieceSquaredBound_nonneg)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Charge the actual four input-support pieces once, before output summation. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 3 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 4 : ℝ) *
        pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  exact ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 4 p) 3 4 (by decide) pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => CoupledTripleCaps.selected_piece_energy p pIn g) f

/-- Orthogonal output pieces give four more energies: the total factor is16. -/
theorem physical_weighted_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 12) f y ^ 2) ≤
      (16 * pieceSquaredBound) * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 12 12 (by decide) f]
  change (∑ p : SelectedSupport 3 4, ∑ y,
    action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 3 4) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 4,
        (ResidualIncidenceCoefficient.multiplicity (3 : Fin 5) 4 : ℝ) *
          pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [selectedSupport_card 3 4 (by decide)]
      norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      ring

/-- The unchanged certificate is compared only after proving physical factor16. -/
theorem certificate_weighted_bound :
    0 ≤ lambda * L 12 12 ∧ 16 * pieceSquaredBound ≤ (lambda * L 12 12) ^ 2 :=
  CoupledTripleScalar.certificate_bound

theorem physical_12_12_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 12) f y ^ 2) ≤
      (lambda * L 12 12) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_weighted_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_weighted_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_12_12_step_cap :
    ‖kernelOperator (physicalBlock 12 12)‖ ≤ lambda * L 12 12 :=
  kernelOperator_norm_le _ certificate_weighted_bound.1 physical_12_12_energy

theorem system_12_12_step_cap :
    ‖PhysicalProjectionSystem.system.step 12 12‖ ≤ lambda * L 12 12 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_12_12_step_cap

end AESConcrete.CoupledTripleStepCaps
