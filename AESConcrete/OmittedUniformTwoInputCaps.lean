import AESConcrete.OmittedUniformTwoInputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction
import AESConcrete.MultiUniformExpansion

/-!
# Original selected-piece transfer for the actual (9,6) minor

The geometry, transport, split, response and scalar modules supply their
respective interfaces.

The original input support is (1,3). Its normalized source is definitionally
the existing multiUniform source with its actual inactive mask retained. The
unrestricted unit-output-vector minor identity applies to every input
function; no input geometry of a different step is substituted. The
same signed residual tuple has exactly the original selected f energy. Its
returned marked-residual fixed-point clause is unused, not a new premise.

This module owns selected-piece transfer. Input support Cauchy, orthogonal
output counting, the factor144 and actual norm endpoints belong to StepCaps.
Constructive fixed AES10/14/16; independent retained keys, whitening, omitted
final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputGeometry (Retained Residual)
open AESConcrete.OmittedUniformTwoInputTransport (normalizedSource)
open AESConcrete.OmittedUniformTwoInputSplit (actualResponse)
open AESConcrete.MultiUniformExpansion (multiUniform)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := OmittedUniformTwoInputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  OmittedUniformTwoInputScalar.C_nonneg

/-- This unfolds two source aliases; it does not identify independently chosen
finite products or discard the original inactive delta. -/
theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h = multiUniform pIn.val.val.2 pIn.val.val.1 h := by
  unfold OmittedUniformTwoInputTransport.normalizedSource
    WeightedResidualLineCaps.normalizedSource
  rfl

/-- General selected tensor/minor equality, before using a response estimate. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq]
  exact OmittedUniformTwoInputResponseEnergy.actualResponse_energy pOut pIn h

/-- Every original f is represented before its selected response is bounded. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (f : AES.WordState → ℝ) :
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

end AESConcrete.OmittedUniformTwoInputCaps
