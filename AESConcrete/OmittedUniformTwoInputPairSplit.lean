import AESConcrete.OmittedUniformTwoInputPairSource
import AESConcrete.OmittedUniformTwoOutputSplit

/-!
# Exact omitted-output split for proposed (9,10)

This module preserves one arbitrary signed JOINT h on the two original
residual input labels, including its zero-pair value, and both original
normalized input uniforms.

W0 is the restriction of that SAME source to the extra physical output zero.
The exact selected minorResponse is identified with the direct physical sum,
then split as R=(W-W0)/sqrt(q-1). No selected-minor energy/operator estimate,
event/plane bound, quantitative desired-bound premise or aggregation is
supplied.

Constructive fixed AES10/14/16; independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoInputPairSplit
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
  (Retained Residual Code input_inactive_not)
open AESConcrete.OmittedUniformTwoInputPairSource
  (normalizedSource uniformWeight bareKernel inputWeightedResponse)
open AESConcrete.OmittedUniformTwoOutputSplit
  (omittedPosition omittedLabel output_partition stateKernel
    outputNormalizer outputNormalizer_eq_sqrt_q outputUniformWeight_eq)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode)
open AESConcrete.WeightedOutputLineCaps (outputUniformWeight)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

theorem bareKernel_eq_stateKernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    bareKernel pOut pIn y c = stateKernel pOut y c.val := rfl

def omittedValue (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : Code pOut pIn) : AES.Word := wordMixAddEquiv c.val (omittedLabel pOut)

def conditionalZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if omittedValue pOut pIn c = 0 then
    normalizedSource pIn h c.val * bareKernel pOut pIn y c else 0

/-- Both nonretained outputs vanish; retain the original input inactive mask. -/
abbrev ExtraZeroCode (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom
    (maskComplement pOut.val.val.1) pIn.val.val.2

/-- W0 keeps both original input weights, on the actual extra-output-zero plane. -/
def extraZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : ExtraZeroCode pOut pIn,
    normalizedSource pIn h c.val * stateKernel pOut y c.val

theorem normalizedSource_on_extraZeroCode (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ)
    (c : ExtraZeroCode pOut pIn) :
    normalizedSource pIn h c.val =
      h (fun i : Residual pIn => c.val i.val) * uniformWeight pIn c.val :=
  OmittedUniformTwoInputPairSource.normalizedSource_eq pIn h c.val

/-- Identity on physical states; no amplitude or uniform-factor transport occurs. -/
def zeroRestrictionEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) :
    {c : Code pOut pIn // omittedValue pOut pIn c = 0} ≃ ExtraZeroCode pOut pIn where
  toFun c := ⟨c.val.val, by
    constructor
    · intro i hi
      rcases (output_partition pOut (omittedPosition pOut) i).mp hi with hi | he
      · exact c.val.property.1 i hi
      · rw [he]
        exact c.property
    · exact c.val.property.2⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · intro i hi
      exact c.property.1 i ((output_partition pOut (omittedPosition pOut) i).mpr (Or.inl hi))
    · exact c.property.2⟩, by
    exact c.property.1 (omittedLabel pOut)
      ((output_partition pOut (omittedPosition pOut) (omittedLabel pOut)).mpr (Or.inr rfl))⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem conditionalZeroResponse_eq_extraZeroResponse
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalZeroResponse pOut pIn h = extraZeroResponse pOut pIn h := by
  funext y
  unfold conditionalZeroResponse extraZeroResponse
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn => omittedValue pOut pIn c = 0),
      normalizedSource pIn h c.val * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn // omittedValue pOut pIn c = 0},
      normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val from
        Finset.sum_subtype _ (by simp) _]
  exact (zeroRestrictionEquiv pOut pIn).sum_comp
    (fun c : ExtraZeroCode pOut pIn =>
      normalizedSource pIn h c.val * stateKernel pOut y c.val)

/-- Direct physical R retains the original input and omitted-output uniforms. -/
def omittedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val *
    outputUniformWeight pOut (wordMixAddEquiv c.val) * bareKernel pOut pIn y c

private theorem omitted_summand (x : AES.Word) (a b : ℝ) :
    a * nonzeroUniform x * b =
      (a * b - (if x = 0 then a * b else 0)) / outputNormalizer := by
  by_cases hx : x = 0 <;>
    simp [nonzeroUniform, supportConstant, identityKernel, hx, outputNormalizer, div_eq_mul_inv]
    <;> ring

/-- Exact R=(W-W0)/sqrt(q-1), preserving the two original input weights. -/
theorem omittedResponse_eq_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
        Real.sqrt (ActivityCodeScalar.q - 1) := by
  funext y
  rw [← conditionalZeroResponse_eq_extraZeroResponse, ← outputNormalizer_eq_sqrt_q]
  unfold omittedResponse inputWeightedResponse conditionalZeroResponse
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [outputUniformWeight_eq]
  exact omitted_summand (omittedValue pOut pIn c)
    (normalizedSource pIn h c.val) (bareKernel pOut pIn y c)

private theorem code_supported_sum (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (F : AES.WordState → ℝ)
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

/-- The actual selected minor response before any quantitative minor estimate. -/
def actualResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 3 pOut)
    (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut) j
          (wordMixAddEquiv x j.val)) =
        (if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
          outputUniformWeight pOut (wordMixAddEquiv x) :=
    WeightedOutputLineCaps.omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x => stateKernel pOut y x *
      ((if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
        outputUniformWeight pOut (wordMixAddEquiv x)) * normalizedSource pIn h x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold stateKernel
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      have ho : ¬ ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 := by
        intro ho
        exact hx ⟨ho, fun i hi => (input_inactive_not pIn i hi).elim⟩
      simp only [F, if_neg ho, zero_mul, mul_zero]
    rw [code_supported_sum pOut pIn F hF]
    unfold omittedResponse
    apply Finset.sum_congr rfl
    intro c _
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    dsimp only [F]
    rw [if_pos ho, one_mul, bareKernel_eq_stateKernel]
    ring

theorem actualResponse_eq_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
        Real.sqrt (ActivityCodeScalar.q - 1) := by
  rw [actualResponse_eq_omittedResponse, omittedResponse_eq_split]

/-- Both exact splits composed; every term uses the same original joint h. -/
theorem actualResponse_eq_four_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      ((OmittedUniformTwoInputPairSource.rawResponse pOut pIn h y -
        OmittedUniformTwoInputPairSource.zeroResponse pOut pIn
          (OmittedUniformTwoInputPairSource.uniformFirst pIn) h y -
        OmittedUniformTwoInputPairSource.zeroResponse pOut pIn
          (OmittedUniformTwoInputPairSource.uniformSecond pIn) h y +
        OmittedUniformTwoInputPairSource.intersectionResponse pOut pIn
          (OmittedUniformTwoInputPairSource.uniformFirst pIn)
          (OmittedUniformTwoInputPairSource.uniformSecond pIn) h y) /
            (ActivityCodeScalar.q - 1) - extraZeroResponse pOut pIn h y) /
              Real.sqrt (ActivityCodeScalar.q - 1) := by
  rw [actualResponse_eq_split, OmittedUniformTwoInputPairSource.inputWeightedResponse_eq_four]

end AESConcrete.OmittedUniformTwoInputPairSplit
