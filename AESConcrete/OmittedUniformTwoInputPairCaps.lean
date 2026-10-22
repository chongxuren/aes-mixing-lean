import AESConcrete.OmittedUniformTwoInputPairResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction
import AESConcrete.MultiUniformExpansion

/-!
# (9,10) selected input transfer

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

namespace AESConcrete.OmittedUniformTwoInputPairCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry (Retained Residual)
open AESConcrete.OmittedUniformTwoInputPairSource (normalizedSource normalizedSource_eq_multiUniform)
open AESConcrete.OmittedUniformTwoInputPairSplit (actualResponse)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := OmittedUniformTwoInputPairScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  OmittedUniformTwoInputPairScalar.C_nonneg

/-- General unit omitted-output embedding, before any response bound is applied. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  -- selectedWordTensor_minor_energy is the unrestricted wrapper around
  -- ActivityMinorContraction.coordinateKernel_rank_one_minor_energy.
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq]
  exact OmittedUniformTwoInputPairResponseEnergy.actualResponse_energy pOut pIn h

/-- The fixed-point property returned by the representation is not an extra premise. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (f : AES.WordState → ℝ) :
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

end AESConcrete.OmittedUniformTwoInputPairCaps
