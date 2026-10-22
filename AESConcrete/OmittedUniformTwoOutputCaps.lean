import AESConcrete.OmittedUniformTwoOutputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction
import AESConcrete.MultiUniformExpansion

/-!
# Original selected-piece transfer for the actual omitted-output response

The general ActivityMinor unit-output-vector identity connects the actual
minor to selectedStepKernel. It applies to every input function and does not
use the output-weighted line geometry's restricted input interface. The
original arbitrary signed residual-singleton tuple has exactly the component's
counting energy. All three input uniforms and the actual omitted output
uniform are already charged by the response theorem; no normalizer is added.

This module owns selected-piece transfer only. Input support Cauchy,
orthogonal output counting, physical energy and certificate conversion belong
in StepCaps. Constructive fixed AES10/14/16, independent uniform retained
keys, whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoOutputCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoOutputGeometry
  (Retained Residual SourceUniformPositions input_inactive_not)
open AESConcrete.OmittedUniformTwoOutputSplit (normalizedSource actualResponse)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion (multiUniform normalizedLeg)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := OmittedUniformTwoOutputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  OmittedUniformTwoOutputScalar.C_nonneg

/-- Input type (1,4) has no inactive label; every original nonresidual label is uniform. -/
def uniformOtherEquiv (pIn : SelectedSupport 1 4) :
    SourceUniformPositions pIn ≃ OtherCoordinates pIn.val.val.1 where
  toFun j := j.val
  invFun j := ⟨j, input_inactive_not pIn j.val⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- Exact source identity, with the same original signed tuple h. -/
theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h = multiUniform pIn.val.val.2 pIn.val.val.1 h := by
  funext x
  unfold OmittedUniformTwoOutputSplit.normalizedSource multiUniform coordinateEmbedding
  rw [counting_prod_instances (X := OtherCoordinates pIn.val.val.1) _ inferInstance]
  have hleg (j : OtherCoordinates pIn.val.val.1) :
      normalizedLeg (AES.maskBit pIn.val.val.2 j.val) (x j.val) =
        nonzeroUniform (x j.val) := by
    simp [normalizedLeg, input_inactive_not pIn j.val]
  simp_rw [hleg]
  exact congrArg (fun a : ℝ => h (fun i : Residual pIn => x i.val) * a)
    ((uniformOtherEquiv pIn).prod_comp
      (fun j : OtherCoordinates pIn.val.val.1 => nonzeroUniform (x j.val)))

/-- General unit omitted-output embedding, before any response bound is applied. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  -- selectedWordTensor_minor_energy is the unrestricted wrapper around
  -- ActivityMinorContraction.coordinateKernel_rank_one_minor_energy.
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq]
  exact OmittedUniformTwoOutputResponseEnergy.actualResponse_energy pOut pIn h

/-- The fixed-point property returned by the representation is not an extra premise. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
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

end AESConcrete.OmittedUniformTwoOutputCaps
