import AESConcrete.TwoOmittedOutputRawInputResponse
import AESConcrete.OmittedUniformTwoInputTransport
import AESConcrete.WeightedResidualLineCaps

/-!
# Same original source on zero, one and two omitted-output restrictions

Output type (2,4), input type (1,3), the original retained labels, inactive
input mask and arbitrary signed residual tuple h, including h(0), are literal
through every restriction. This file owns geometry and exact sum transports;
it supplies no analytic bound, minor transfer or physical endpoint.
Constructive fixed AES10/14/16; independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry
open AESConcrete.TwoOmittedOutputRawResponse (bareKernel)
open AESConcrete.TwoOmittedOutputRawInputResponse (normalizedSource inputWeightedResponse)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

-- Finite support identities precede the classical predicate instance. Their
-- tactic bodies are source text only, not executed finite checks.
theorem complement_facts : ∀ E : Fin 16, maskSize E = 2 →
    MaskDisjoint (maskComplement E) E ∧ maskSize (maskComplement E) + 2 = 4 := by decide

theorem complement_partition : ∀ E : Fin 16, maskSize E = 2 →
    ∀ a b : Fin 4, maskBit E a ≠ true → maskBit E b ≠ true → a ≠ b →
      ∀ i : Fin 4, maskBit (maskComplement E) i = true ↔ i = a ∨ i = b := by
  -- Keep each finite decision closed: first split all labels, then reduce
  -- the complete implication. norm_num alone does not normalize Nat.testBit.
  intro E hE a b ha hb hab i
  revert hE ha hb hab
  fin_cases E <;> fin_cases a <;> fin_cases b <;> fin_cases i <;> decide

attribute [local instance] Classical.propDecidable

theorem output_inactive_not (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit pOut.val.val.2 i ≠ true := by
  intro hi
  have hc : 0 < Fintype.card (MaskCoordinates pOut.val.val.2) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [maskCoordinates_card, outputInactiveMask_size] at hc
  omega

/-- All nonretained output labels are original omitted nonzero uniforms. -/
abbrev Omitted (pOut : SelectedSupport 2 4) := OtherCoordinates pOut.val.val.1

theorem omitted_card (pOut : SelectedSupport 2 4) : Fintype.card (Omitted pOut) = 2 := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, retainedMask_size]

def omittedIndexEquiv (pOut : SelectedSupport 2 4) : Omitted pOut ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [omitted_card]; simp)

def omittedFirst (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 0

def omittedSecond (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 1

theorem omittedFirst_ne_second (pOut : SelectedSupport 2 4) :
    omittedFirst pOut ≠ omittedSecond pOut :=
  (omittedIndexEquiv pOut).symm.injective.ne (by decide)

theorem omitted_labels_ne (pOut : SelectedSupport 2 4) :
    (omittedFirst pOut).val ≠ (omittedSecond pOut).val := by
  intro he
  exact omittedFirst_ne_second pOut (Subtype.ext he)

/-- Set one original omitted output to zero; preserve E and all input masks. -/
def oneZero (pOut : SelectedSupport 2 4) (a : Omitted pOut) : SelectedSupport 2 3 :=
  ⟨⟨(pOut.val.val.1, singletonMask a.val), ⟨by
    intro i hi hE
    have he : i = a.val := (singletonMask_bit _ _).mp hi
    subst i
    exact a.property hE, pOut.val.property.2⟩⟩, by norm_num [singletonMask_size]⟩

/-- Set both original omitted outputs to zero; preserve the literal E. -/
def twoZero (pOut : SelectedSupport 2 4) : SelectedSupport 2 2 :=
  ⟨⟨(pOut.val.val.1, maskComplement pOut.val.val.1),
    ⟨(complement_facts _ pOut.val.property.2).1, pOut.val.property.2⟩⟩,
    (complement_facts _ pOut.val.property.2).2⟩

theorem twoZero_partition (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit (twoZero pOut).val.val.2 i = true ↔
      i = (omittedFirst pOut).val ∨ i = (omittedSecond pOut).val :=
  complement_partition _ (retainedMask_size pOut) _ _
    (omittedFirst pOut).property (omittedSecond pOut).property (omitted_labels_ne pOut) i

def omittedValue (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (a : Omitted pOut) (c : Code pOut pIn) : AES.Word := wordMixAddEquiv c.val a.val

def singleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (fun c : Code pOut pIn => normalizedSource pIn h c.val)
    (bareKernel pOut pIn) (omittedValue pOut pIn a)

def doubleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse
    (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn)
    (omittedValue pOut pIn (omittedFirst pOut))
    (omittedValue pOut pIn (omittedSecond pOut))

def oneZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  OmittedUniformTwoInputTransport.inputWeightedResponse (oneZero pOut a) pIn h

def twoZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResidualLineCaps.response (twoZero pOut) pIn (normalizedSource pIn h)

/-- Identity on physical inputs; only the actual output restriction changes. -/
def singleRestrictionEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (a : Omitted pOut) :
    {c : Code pOut pIn // omittedValue pOut pIn a c = 0} ≃
      OmittedUniformTwoInputGeometry.Code (oneZero pOut a) pIn where
  toFun c := ⟨c.val.val, by
    constructor
    · intro i hi
      have he : i = a.val := (singletonMask_bit _ _).mp hi
      rw [he]
      exact c.property
    · exact c.val.property.2⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · intro i hi
      exact (output_inactive_not pOut i hi).elim
    · exact c.property.2⟩, by
      exact c.property.1 a.val ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem singleConditionalResponse_eq_oneZeroResponse
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3) (a : Omitted pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    singleConditionalResponse pOut pIn a h = oneZeroResponse pOut pIn a h := by
  funext y
  unfold singleConditionalResponse WeightedResponse.zeroResponse oneZeroResponse
    OmittedUniformTwoInputTransport.inputWeightedResponse
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn =>
      omittedValue pOut pIn a c = 0), normalizedSource pIn h c.val * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn // omittedValue pOut pIn a c = 0},
      normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val from
        Finset.sum_subtype _ (by simp) _]
  exact (singleRestrictionEquiv pOut pIn a).sum_comp
    (fun c : OmittedUniformTwoInputGeometry.Code (oneZero pOut a) pIn =>
      OmittedUniformTwoInputTransport.normalizedSource pIn h c.val *
        OmittedUniformTwoInputGeometry.bareKernel (oneZero pOut a) pIn y c)

def doubleRestrictionEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3) :
    {c : Code pOut pIn //
      omittedValue pOut pIn (omittedFirst pOut) c = 0 ∧
      omittedValue pOut pIn (omittedSecond pOut) c = 0} ≃
        WeightedResidualLineGeometry.LineCode (twoZero pOut) pIn where
  toFun c := ⟨c.val.val, by
    constructor
    · intro i hi
      rcases (twoZero_partition pOut i).mp hi with he | he
      · rw [he]
        exact c.property.1
      · rw [he]
        exact c.property.2
    · exact c.val.property.2⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · intro i hi
      exact (output_inactive_not pOut i hi).elim
    · exact c.property.2⟩, by
      constructor
      · exact c.property.1 _ ((twoZero_partition pOut _).mpr (Or.inl rfl))
      · exact c.property.1 _ ((twoZero_partition pOut _).mpr (Or.inr rfl))⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem doubleConditionalResponse_eq_twoZeroResponse
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    doubleConditionalResponse pOut pIn h = twoZeroResponse pOut pIn h := by
  funext y
  unfold doubleConditionalResponse TripleResponse.intersectionResponse twoZeroResponse
    WeightedResidualLineCaps.response IndexedTripleEnergy.response
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn =>
      omittedValue pOut pIn (omittedFirst pOut) c = 0 ∧
      omittedValue pOut pIn (omittedSecond pOut) c = 0),
        normalizedSource pIn h c.val * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn //
      omittedValue pOut pIn (omittedFirst pOut) c = 0 ∧
      omittedValue pOut pIn (omittedSecond pOut) c = 0},
        normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val from
          Finset.sum_subtype _ (by simp) _]
  exact (doubleRestrictionEquiv pOut pIn).sum_comp
    (fun c : WeightedResidualLineGeometry.LineCode (twoZero pOut) pIn =>
      normalizedSource pIn h c.val * ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i)
          (WeightedResidualLineGeometry.curve (twoZero pOut) pIn c i))

theorem twoZeroResponse_eq_jointResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    twoZeroResponse pOut pIn h =
      WeightedResidualLineCaps.jointResponse (twoZero pOut) pIn h :=
  WeightedResidualLineCaps.response_normalizedSource (twoZero pOut) pIn h

end AESConcrete.TwoOmittedOutputSource
