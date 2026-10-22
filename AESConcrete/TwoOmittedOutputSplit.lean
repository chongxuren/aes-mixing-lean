import AESConcrete.TwoOmittedOutputSource
import AESConcrete.ActivityMinorContraction
import AESConcrete.ActivityMinor

/-!
# Exact two-output inclusion-exclusion for the original (10,6) source

The actual retained minor is identified with R=(W-W_a-W_b+W_ab)/(q-1), using
the same original normalized input source on every restriction. Both output
nonzero uniforms are expanded; the original input delta and both input
uniforms remain inside all four terms. This file proves finite identities
only, with no response bound as a premise.

Constructive fixed AES10/14/16; independent retained keys, whitening, omitted
final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputSplit
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry
open AESConcrete.TwoOmittedOutputRawResponse (bareKernel)
open AESConcrete.TwoOmittedOutputRawInputResponse (normalizedSource inputWeightedResponse)
open AESConcrete.TwoOmittedOutputSource
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

def outputUniformWeight (pOut : SelectedSupport 2 4) (x : AES.WordState) : ℝ :=
  ∏ a : Omitted pOut, nonzeroUniform (x a.val)

theorem outputUniformWeight_eq_two (pOut : SelectedSupport 2 4) (x : AES.WordState) :
    outputUniformWeight pOut x = nonzeroUniform (x (omittedFirst pOut).val) *
      nonzeroUniform (x (omittedSecond pOut).val) := by
  have he := (omittedIndexEquiv pOut).symm.prod_comp
    (fun a : Omitted pOut => nonzeroUniform (x a.val))
  simpa only [Fin.prod_univ_two, omittedFirst, omittedSecond, outputUniformWeight]
    using he.symm

theorem omittedWeight_product (pOut : SelectedSupport 2 4) (x : AES.WordState) :
    (∏ j : OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j (x j.val)) =
        outputUniformWeight pOut x := by
  unfold outputUniformWeight
  apply Finset.prod_congr rfl
  intro j _
  -- Reduce the Bool-to-Prop equality left by the inactive-mask rewrite.
  simp [nonzeroWeight, selectedZeros, output_inactive_not pOut j.val]

def stateKernel (pOut : SelectedSupport 2 4) (y : Retained pOut → AES.Word)
    (x : AES.WordState) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)

theorem bareKernel_eq_stateKernel (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    bareKernel pOut pIn y c = stateKernel pOut y c.val := rfl

def omittedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val *
    outputUniformWeight pOut (wordMixAddEquiv c.val) * bareKernel pOut pIn y c

theorem omittedResponse_eq_two (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = TripleResponse.weightedResponse
      (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn)
      (omittedValue pOut pIn (omittedFirst pOut))
      (omittedValue pOut pIn (omittedSecond pOut)) := by
  funext y
  unfold omittedResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [outputUniformWeight_eq_two]
  unfold omittedValue
  ring

/-- No input factor is expanded or renormalized in this output split. -/
theorem omittedResponse_eq_split (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        oneZeroResponse pOut pIn (omittedFirst pOut) h y -
        oneZeroResponse pOut pIn (omittedSecond pOut) h y +
        twoZeroResponse pOut pIn h y) / (q - 1) := by
  rw [omittedResponse_eq_two, TripleResponse.weightedResponse_eq_four]
  have hn := TripleResponse.normalizer_eq AES.Word AES.word_card_gt_one.le
  rw [DoubleUniformFourierEnergy.word_card_real] at hn
  have hraw : WeightedResponse.rawResponse
      (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn) =
        inputWeightedResponse pOut pIn h := rfl
  rw [hraw, hn]
  change (fun y => (inputWeightedResponse pOut pIn h y -
      singleConditionalResponse pOut pIn (omittedFirst pOut) h y -
      singleConditionalResponse pOut pIn (omittedSecond pOut) h y +
      doubleConditionalResponse pOut pIn h y) / (q - 1)) = _
  rw [singleConditionalResponse_eq_oneZeroResponse,
    singleConditionalResponse_eq_oneZeroResponse, doubleConditionalResponse_eq_twoZeroResponse]

private theorem code_supported_sum (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (F : AES.WordState → ℝ)
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

def actualResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 4 pOut)
    (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j
          (wordMixAddEquiv x j.val)) = outputUniformWeight pOut (wordMixAddEquiv x) :=
    omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x =>
    stateKernel pOut y x * outputUniformWeight pOut (wordMixAddEquiv x) * normalizedSource pIn h x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold stateKernel
    unfold selectedRetained at hw
    rw [counting_prod_instances (X := OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      have hG : normalizedSource pIn h x = 0 := by
        by_contra hn
        apply hx
        constructor
        · intro i hi
          exact (output_inactive_not pOut i hi).elim
        · exact WeightedResidualLineCaps.normalizedSource_supported pIn h x hn
      simp only [F, hG, mul_zero]
    rw [code_supported_sum pOut pIn F hF]
    unfold omittedResponse
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [F]
    rw [bareKernel_eq_stateKernel]
    ring

theorem actualResponse_eq_split (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        oneZeroResponse pOut pIn (omittedFirst pOut) h y -
        oneZeroResponse pOut pIn (omittedSecond pOut) h y +
        twoZeroResponse pOut pIn h y) / (q - 1) := by
  rw [actualResponse_eq_omittedResponse, omittedResponse_eq_split]

end AESConcrete.TwoOmittedOutputSplit
