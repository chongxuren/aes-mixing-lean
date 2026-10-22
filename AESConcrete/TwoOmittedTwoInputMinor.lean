import AESConcrete.TwoOmittedTwoInputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction

/-!
Lemmas for (10,10). The original exact minor is reindexed by actual diffusion,
with both omitted output U factors retained. Unit output energies introduce no
new denominator. Arbitrary original input pieces use the unchanged
multiUniform representation; its extra fixed-point property is unused.
Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedTwoInputMinor
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedTwoInputSource
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
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

theorem omittedWeight_product (pOut : SelectedSupport 2 4) (x : AES.WordState) :
    (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j (x j.val)) =
      nonzeroUniform (x (omittedFirst pOut).val) * nonzeroUniform (x (omittedSecond pOut).val) := by
  have hp : (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j (x j.val)) =
      ∏ j : Omitted pOut, nonzeroUniform (x j.val) := by
    rw [counting_prod_instances (X := Omitted pOut) _ inferInstance]
    apply Finset.prod_congr rfl
    intro j _
    simp [nonzeroWeight, selectedZeros, empty_inactive pOut j.val]
  rw [hp]
  have he := (omittedIndexEquiv pOut).symm.prod_comp (fun j : Omitted pOut => nonzeroUniform (x j.val))
  simpa only [Fin.prod_univ_two, omittedFirst, omittedSecond] using he.symm

def actualResponse (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 4 pOut) (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  unfold omittedResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro x _
  have hw := omittedWeight_product pOut (wordMixAddEquiv x)
  unfold selectedRetained at hw
  rw [counting_prod_instances (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
    hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  unfold bareKernel outputValue
  ring

theorem selectedStep_energy_eq (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut) (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _ (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

abbrev pieceSquaredBound : ℝ := TwoOmittedTwoInputScalar.C
theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := TwoOmittedTwoInputScalar.C_nonneg

theorem selected_normalizedSource_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut) (normalizedSource pIn h) y ^ 2) ≤
      pieceSquaredBound * ∑ r, h r ^ 2 := by
  rw [selectedStep_energy_eq, actualResponse_eq_omittedResponse]
  -- Fix the provider's counting space in the intermediate expression explicitly.
  calc
    _ = ∑ y : Retained pOut → AES.Word, omittedResponse pOut pIn h y ^ 2 :=
      counting_sum_instances _ _ _
    _ ≤ _ := TwoOmittedTwoInputResponseEnergy.omittedResponse_energy pOut pIn h

theorem selected_piece_energy (pOut pIn : SelectedSupport 2 4) (f : AES.WordState → ℝ) :
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
end AESConcrete.TwoOmittedTwoInputMinor
