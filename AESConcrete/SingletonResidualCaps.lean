import AESConcrete.ActivityMinorBounds
import AESConcrete.SingletonResidualEnergy

/-!
# Physical aggregation of the signed singleton graph bound

The selected-piece estimate retains an arbitrary signed input. Four genuine
input support pieces cost one Cauchy--Schwarz factor; the four physical output
support energies add by orthogonality. The numerical certificate comparison
comes after this physical argument. This new source is a candidate until its
compilation and independent review; accepted sources remain frozen.

Constructive mathematics only; no attacks or manuscript changes. Independent
uniform retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.SingletonResidualCaps
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorInput
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

def pieceSquaredBound : ℝ :=
  (21 / 131072 : ℝ) ^ 2 * (2 / (15 * 4294967296) : ℝ) ^ 2 /
    (4294967296 - 1)

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := by
  norm_num [pieceSquaredBound]

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- The input multiplicity four is charged once; arbitrary signs remain. -/
theorem selected_refined_input_energy (p : SelectedSupport 3 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 1) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤
      4 * pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [← selectedStepKernel_action,
    ← ResidualIncidenceAggregation.selected_action_sum, action_fintype_sum]
  have he := ActivityMinorCaps.selected_output_energy_of_piece_energy
    (selectedStepKernel 3 4 p) 1 1 (by decide)
    pieceSquaredBound pieceSquaredBound_nonneg
    (fun pIn g => SingletonResidualEnergy.selected_piece_energy p pIn g) f
  simpa [ResidualIncidenceCoefficient.multiplicity, Nat.choose] using he

/-- The four actual output energies are orthogonal after the full step. -/
theorem physical_singleton_graph_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 4) f y ^ 2) ≤
      16 * pieceSquaredBound * ∑ x, f x ^ 2 := by
  rw [physicalBlock_selected_tensor_energy 12 4 (by decide) f]
  change (∑ p : SelectedSupport 3 4, ∑ y,
    action (selectedWordTensor 3 4 p)
      (fun x => action (refinedKernel (0 : AES.Word) 1 1) f
        (wordMixAddEquiv.symm x)) y ^ 2) ≤ _
  calc
    _ ≤ ∑ _p : SelectedSupport 3 4,
        (4 : ℝ) * pieceSquaredBound * ∑ x, f x ^ 2 :=
      Finset.sum_le_sum (fun p _ => selected_refined_input_energy p f)
    _ = _ := by
      have hcard : Fintype.card (SelectedSupport (3 : Fin 5) 4) = 4 := by
        rw [selectedSupport_card 3 4 (by decide)]
        norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
        Nat.cast_ofNat]
      ring

/-- Exact scalar comparison, separate from the signed physical estimate. -/
theorem certificate_singleton_bound :
    0 ≤ lambda * L 12 4 ∧
      16 * pieceSquaredBound ≤ (lambda * L 12 4) ^ 2 := by
  norm_num [pieceSquaredBound, AESRound.Terminal.lambda, AESRound.Certificate.L]

theorem physical_singleton_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 12 4) f y ^ 2) ≤
      (lambda * L 12 4) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_singleton_graph_energy f).trans
    (mul_le_mul_of_nonneg_right certificate_singleton_bound.2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

theorem physical_singleton_step_cap :
    ‖kernelOperator (physicalBlock 12 4)‖ ≤ lambda * L 12 4 :=
  kernelOperator_norm_le _ certificate_singleton_bound.1 physical_singleton_energy

theorem system_singleton_step_cap :
    ‖PhysicalProjectionSystem.system.step 12 4‖ ≤ lambda * L 12 4 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_singleton_step_cap

end AESConcrete.SingletonResidualCaps
