import AESConcrete.TwoOmittedOneInputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.MultiUniformExpansion

/-!
# original selected-piece transfer for (10,12)

Exact normalized-source and minor identities precede analytic inequalities.
MultiUniformExpansion supplies arbitrary signed h for every original support
piece, including h(0). Its marked-residual fixed-point clause is not used as
an extra premise. Support multiplicities and physical aggregation belong in
StepCaps. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry (Retained Residual)
open AESConcrete.TwoOmittedOneInputSource (normalizedSource)
open AESConcrete.TwoOmittedOneInputSplit (actualResponse)
open AESConcrete.MultiUniformExpansion (multiUniform)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := TwoOmittedOneInputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := TwoOmittedOneInputScalar.C_nonneg

theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h = multiUniform pIn.val.val.2 pIn.val.val.1 h :=
  TwoOmittedOneInputSource.normalizedSource_eq_multiUniform pIn h

theorem selectedStep_energy_eq (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (normalizedSource pIn h) y ^ 2) = ∑ y, actualResponse pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ r, h r ^ 2 := by
  rw [selectedStep_energy_eq]
  exact TwoOmittedOneInputResponseEnergy.actualResponse_energy pOut pIn h

/-- Every original f is represented before its response is bounded. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (f : AES.WordState → ℝ) :
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

end AESConcrete.TwoOmittedOneInputCaps
