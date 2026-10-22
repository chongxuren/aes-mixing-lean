import AESConcrete.OmittedUniformTwoInputTransport
import AESConcrete.OmittedUniformTwoOutputSplit

/-!
# Omitted-output split with one actual input zero

The two input uniforms stay inside W and W0. The actual minor is identified
before any analytic estimate is used. Fixed constructive AES10/14/16 only.

W0 is the WeightedResidualLine response of the same normalized source, with
the original input-zero mask, both retained labels and signed h unchanged.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputSplit
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputGeometry
open AESConcrete.OmittedUniformTwoInputTransport (normalizedSource inputWeightedResponse)
open AESConcrete.OmittedUniformTwoOutputSplit
  (zeroCompletion omittedPosition omittedLabel output_partition stateKernel
    outputNormalizer outputNormalizer_eq_sqrt_q outputUniformWeight_eq)
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

theorem bareKernel_eq_stateKernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    bareKernel pOut pIn y c = stateKernel pOut y c.val := rfl

def omittedValue (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (c : Code pOut pIn) : AES.Word := wordMixAddEquiv c.val (omittedLabel pOut)

def conditionalZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if omittedValue pOut pIn c = 0 then
    normalizedSource pIn h c.val * bareKernel pOut pIn y c else 0

/-- W0 is the original normalized source on the actual three-zero line. -/
def extraZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResidualLineCaps.response (zeroCompletion pOut) pIn (normalizedSource pIn h)

/-- This equivalence preserves the original input-zero condition, unlike a plane
whose input mask is empty. Its values are the identity on physical states. -/
def zeroRestrictionEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3) :
    {c : Code pOut pIn // omittedValue pOut pIn c = 0} ≃
      WeightedResidualLineGeometry.LineCode (zeroCompletion pOut) pIn where
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
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalZeroResponse pOut pIn h = extraZeroResponse pOut pIn h := by
  funext y
  unfold conditionalZeroResponse extraZeroResponse WeightedResidualLineCaps.response
    IndexedTripleEnergy.response
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn => omittedValue pOut pIn c = 0),
      normalizedSource pIn h c.val * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn // omittedValue pOut pIn c = 0},
      normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val from
        Finset.sum_subtype _ (by simp) _]
  exact (zeroRestrictionEquiv pOut pIn).sum_comp
    (fun c => normalizedSource pIn h c.val *
      ∏ i : WeightedResidualLineGeometry.Retained (zeroCompletion pOut),
        residualMatrix AES.wordSuperboxKernel 0 (y i)
          (WeightedResidualLineGeometry.curve (zeroCompletion pOut) pIn c i))

theorem extraZeroResponse_eq_jointResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    extraZeroResponse pOut pIn h =
      WeightedResidualLineCaps.jointResponse (zeroCompletion pOut) pIn h :=
  WeightedResidualLineCaps.response_normalizedSource (zeroCompletion pOut) pIn h

def omittedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val *
    outputUniformWeight pOut (wordMixAddEquiv c.val) * bareKernel pOut pIn y c

private theorem omitted_summand (x : AES.Word) (a b : ℝ) :
    a * nonzeroUniform x * b =
      (a * b - (if x = 0 then a * b else 0)) / outputNormalizer := by
  by_cases hx : x = 0 <;>
    simp [nonzeroUniform, supportConstant, identityKernel, hx, outputNormalizer, div_eq_mul_inv]
    <;> ring

theorem omittedResponse_eq_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
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

def actualResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 3 pOut)
    (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
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
      by_cases ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0
      · have hi : ¬ ∀ i, maskBit pIn.val.val.2 i = true → x i = 0 :=
          fun hi => hx ⟨ho, hi⟩
        have hG : normalizedSource pIn h x = 0 := by
          by_contra hn
          apply hi
          exact WeightedResidualLineCaps.normalizedSource_supported pIn h x hn
        simp only [F, hG, mul_zero]
      · simp only [F, if_neg ho, zero_mul, mul_zero]
    rw [code_supported_sum pOut pIn F hF]
    unfold omittedResponse
    apply Finset.sum_congr rfl
    intro c _
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    dsimp only [F]
    rw [if_pos ho, one_mul, bareKernel_eq_stateKernel]
    ring

theorem actualResponse_eq_split (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
        Real.sqrt (ActivityCodeScalar.q - 1) := by
  rw [actualResponse_eq_omittedResponse, omittedResponse_eq_split]

end AESConcrete.OmittedUniformTwoInputSplit
