import AESConcrete.OmittedPairOneInputResponseEnergy
import AESConcrete.ActivityMinorInput
import AESConcrete.ActivityMinorContraction

/-!
Lemmas for (10,9). The exact selected minor is transported to the original
physical code before using the response estimate. Both omitted output legs are
the original U. Their unit output-vector energies insert no extra
normalization. Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedPairOneInputMinor
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedPairOneInputRawGeometry
open AESConcrete.OmittedPairOneInputSource
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
      nonzeroUniform (x (omittedFirst pOut).val) *
        nonzeroUniform (x (omittedSecond pOut).val) := by
  have hp : (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j (x j.val)) =
      ∏ j : Omitted pOut, nonzeroUniform (x j.val) := by
    rw [counting_prod_instances (X := Omitted pOut) _ inferInstance]
    apply Finset.prod_congr rfl
    intro j _
    simp [nonzeroWeight, selectedZeros, output_inactive_not pOut j.val]
  rw [hp]
  have he := (omittedIndexEquiv pOut).symm.prod_comp
    (fun j : Omitted pOut => nonzeroUniform (x j.val))
  simpa only [Fin.prod_univ_two, omittedFirst, omittedSecond] using he.symm

private theorem code_supported_sum (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 x → F x = 0) :
    (∑ x, F x) = ∑ c : Code pOut pIn, F c.val := by
  calc
    _ = ∑ x, if graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · exact hF x hx
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _
        (by intro x; simp [ShortenedWeightedGeometry.shortenedSubgroup]) _

def actualResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 4 pOut)
    (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

/-- Exact minor identity; no energy estimate or altered source enters it. -/
theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  let F : AES.WordState → ℝ := fun x =>
    normalizedSource pIn h x *
      nonzeroUniform (wordMixAddEquiv x (omittedFirst pOut).val) *
      nonzeroUniform (wordMixAddEquiv x (omittedSecond pOut).val) *
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    have hw := omittedWeight_product pOut (wordMixAddEquiv x)
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
    dsimp only [F]
    ring
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      have hg : normalizedSource pIn h x = 0 := by
        by_contra hG
        apply hx
        constructor
        · intro i hi
          exact (output_inactive_not pOut i hi).elim
        · exact WeightedResidualLineCaps.normalizedSource_supported pIn h x hG
      simp [F, hg]
    rw [code_supported_sum pOut pIn F hF]
    rfl

/-- General unit omitted-output embedding, before any response bound. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut) (normalizedSource pIn h) y ^ 2) =
      ∑ y, actualResponse pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, ActivityMinor.selectedWordTensor_minor_energy]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => actualResponse pOut pIn h y ^ 2)

abbrev pieceSquaredBound : ℝ := OmittedPairOneInputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound := OmittedPairOneInputScalar.C_nonneg

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut) (normalizedSource pIn h) y ^ 2) ≤
      pieceSquaredBound * ∑ r, h r ^ 2 := by
  rw [selectedStep_energy_eq, actualResponse_eq_omittedResponse]
  have he := OmittedPairOneInputResponseEnergy.omittedResponse_energy pOut pIn h
  -- The selected retained alias and the provider have equal counting instances.
  convert he using 1 <;>
    first
    | rfl
    | exact counting_sum_instances _ _
        (fun y : Retained pOut → AES.Word => omittedResponse pOut pIn h y ^ 2)

/-- Representation provides the same joint h and exact input energy.
The additional fixed-point property is deliberately unused. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (f : AES.WordState → ℝ) :
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
end AESConcrete.OmittedPairOneInputMinor
