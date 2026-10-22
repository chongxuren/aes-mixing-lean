import AESConcrete.TwoOmittedOutputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction
import AESConcrete.MultiUniformExpansion

/-!
# Original selected-piece transfer for (10,6)

The original input (1,3) normalized source retains its inactive mask and
signed residual tuple h, including h(0). The unrestricted unit omitted-output-
vector minor identity applies before the response estimate. The returned
marked- residual fixed-point clause is unused; it is not an extra source
premise. This component owns selected-piece transfer. Physical input factor12
and six orthogonal output energies belong in StepCaps. Constructive fixed
AES10/14/16, independent retained keys, whitening, omitted final MixColumns,
ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry (Retained Residual)
open AESConcrete.TwoOmittedOutputRawInputResponse (normalizedSource)
open AESConcrete.TwoOmittedOutputSplit (actualResponse)
open AESConcrete.MultiUniformExpansion (multiUniform)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := TwoOmittedOutputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  TwoOmittedOutputScalar.C_nonneg

/-- This unfolds two source aliases; it does not identify independently chosen
finite products or discard the original inactive delta. -/
theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h = multiUniform pIn.val.val.2 pIn.val.val.1 h := by
  unfold TwoOmittedOutputRawInputResponse.normalizedSource
    WeightedResidualLineCaps.normalizedSource
  rfl

/-- General selected tensor/minor equality, before using a response estimate. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq]
  exact TwoOmittedOutputResponseEnergy.actualResponse_energy pOut pIn h

/-- Every original f is represented before its selected response is bounded. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have heq : supportIndexComponent (0 : AES.Word) pIn.val f = normalizedSource pIn h :=
    hc.trans (normalizedSource_eq_multiUniform pIn h).symm
  have ht := selected_normalizedSource_energy pOut pIn h
  rw [henergy, heq]
  exact ht

end AESConcrete.TwoOmittedOutputCaps
