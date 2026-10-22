import AESConcrete.TwoOmittedTwoInputSingleRawEnergy
import AESConcrete.OmittedUniformTwoInputPairSource
import AESConcrete.WordMixedCentering

/-!
Lemmas for (10,10). Only its original normalized input interface is reused:
both original input U factors and the arbitrary signed JOINT h, including the
zero pair. No (9,10) physical endpoint or extra omitted output U is
introduced. Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedTwoInputSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)
set_option maxRecDepth 100000

abbrev Retained (pOut : SelectedSupport 2 4) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 2 4) := MaskCoordinates pIn.val.val.1
abbrev InputUniformPositions (pIn : SelectedSupport 2 4) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1
abbrev Omitted (pOut : SelectedSupport 2 4) :=
  GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1

-- These are finite mask facts; no word-space enumeration occurs.
theorem empty_inactive : ∀ (p : SelectedSupport 2 4) (i : Fin 4),
    maskBit p.val.val.2 i ≠ true := by decide

theorem oneZero_mask_facts : ∀ (p : SelectedSupport 2 4) (a : Omitted p),
    MaskDisjoint (singletonMask a.val) p.val.val.1 ∧
      maskSize (singletonMask a.val) + 3 = 4 := by decide

theorem completion_mask_facts : ∀ r : Fin 16, maskSize r = 2 →
    MaskDisjoint (maskComplement r) r ∧ maskSize (maskComplement r) + 2 = 4 := by decide

theorem omitted_pair_partition : ∀ (p : SelectedSupport 2 4) (a b : Omitted p),
    a ≠ b → ∀ i : Fin 4,
    maskBit (maskComplement p.val.val.1) i = true ↔ i = a.val ∨ i = b.val := by decide

attribute [local instance] Classical.propDecidable

theorem retainedMask_size (pOut : SelectedSupport 2 4) : maskSize pOut.val.val.1 = 2 :=
  OmittedUniformTwoInputRawGeometry.residualMask_size pOut

theorem retainedCoordinates_card (pOut : SelectedSupport 2 4) : Fintype.card (Retained pOut) = 2 := by
  rw [maskCoordinates_card, retainedMask_size]

abbrev normalizedSource (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  OmittedUniformTwoInputPairSource.normalizedSource pIn h
abbrev uniformFirst (pIn : SelectedSupport 2 4) := OmittedUniformTwoInputPairSource.uniformFirst pIn
abbrev uniformSecond (pIn : SelectedSupport 2 4) := OmittedUniformTwoInputPairSource.uniformSecond pIn

theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : normalizedSource pIn h =
      MultiUniformExpansion.multiUniform pIn.val.val.2 pIn.val.val.1 h := rfl

theorem normalizedSource_energy (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ r, h r ^ 2 :=
  OmittedUniformTwoInputPairSource.normalizedSource_energy pIn h

theorem normalizedSource_eq_two (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    normalizedSource pIn h x = h (fun i => x i.val) *
      nonzeroUniform (x (uniformFirst pIn).val.val) *
      nonzeroUniform (x (uniformSecond pIn).val.val) := by
  change OmittedUniformTwoInputPairSource.normalizedSource pIn h x = _
  rw [OmittedUniformTwoInputPairSource.normalizedSource_eq,
    OmittedUniformTwoInputPairSource.uniformWeight_eq_two]
  simp only [uniformFirst, uniformSecond]
  ring

def bareKernel (pOut : SelectedSupport 2 4) (y : Retained pOut → AES.Word) (x : AES.WordState) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)

def rawResponse (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)

def inputZeroResponse (pOut pIn : SelectedSupport 2 4) (t : InputUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (fun x : AES.WordState => h (fun i => x i.val))
    (bareKernel pOut) (fun x => x t.val.val)

def inputIntersectionResponse (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse (fun x : AES.WordState => h (fun i => x i.val))
    (bareKernel pOut) (fun x => x (uniformFirst pIn).val.val) (fun x => x (uniformSecond pIn).val.val)

def inputWeightedResponse (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (normalizedSource pIn h) (bareKernel pOut)

theorem inputWeightedResponse_eq_two (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = TripleResponse.weightedResponse
      (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)
      (fun x => x (uniformFirst pIn).val.val) (fun x => x (uniformSecond pIn).val.val) := by
  funext y
  unfold inputWeightedResponse WeightedResponse.rawResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [normalizedSource_eq_two]

theorem inputWeightedResponse_eq_four (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y - inputZeroResponse pOut pIn (uniformFirst pIn) h y -
        inputZeroResponse pOut pIn (uniformSecond pIn) h y +
        inputIntersectionResponse pOut pIn h y) / (q - 1) := by
  rw [inputWeightedResponse_eq_two, TripleResponse.weightedResponse_eq_four,
    TripleResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one), word_card_real]
  rfl

def omittedIndexEquiv (pOut : SelectedSupport 2 4) : Omitted pOut ≃ Fin 2 :=
  Fintype.equivOfCardEq (by
    change Fintype.card {i : Fin 4 // ¬ maskBit pOut.val.val.1 i = true} = Fintype.card (Fin 2)
    rw [Fintype.card_subtype_compl, maskCoordinates_card, retainedMask_size]
    decide)
def omittedFirst (pOut : SelectedSupport 2 4) := (omittedIndexEquiv pOut).symm 0
def omittedSecond (pOut : SelectedSupport 2 4) := (omittedIndexEquiv pOut).symm 1

theorem omittedFirst_ne_second (pOut : SelectedSupport 2 4) : omittedFirst pOut ≠ omittedSecond pOut := by
  intro he
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [omittedFirst, omittedSecond, Equiv.apply_symm_apply] using
      congrArg (omittedIndexEquiv pOut) he
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def outputValue (pOut : SelectedSupport 2 4) (a : Omitted pOut) (x : AES.WordState) := wordMixAddEquiv x a.val

def outputZeroResponse (pOut pIn : SelectedSupport 2 4) (a : Omitted pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (normalizedSource pIn h) (bareKernel pOut) (outputValue pOut a)

def outputIntersectionResponse (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse (normalizedSource pIn h) (bareKernel pOut)
    (outputValue pOut (omittedFirst pOut)) (outputValue pOut (omittedSecond pOut))

def omittedResponse (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.weightedResponse (normalizedSource pIn h) (bareKernel pOut)
    (outputValue pOut (omittedFirst pOut)) (outputValue pOut (omittedSecond pOut))

theorem omittedResponse_eq_four (pOut pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y - outputZeroResponse pOut pIn (omittedFirst pOut) h y -
        outputZeroResponse pOut pIn (omittedSecond pOut) h y +
        outputIntersectionResponse pOut pIn h y) / (q - 1) := by
  unfold omittedResponse
  rw [TripleResponse.weightedResponse_eq_four,
    TripleResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one), word_card_real]
  rfl

/-- Change only the inactive output mask; E, pIn and h remain original. -/
def oneZero (pOut : SelectedSupport 2 4) (a : Omitted pOut) : SelectedSupport 2 3 :=
  ⟨⟨(pOut.val.val.1, singletonMask a.val), ⟨(oneZero_mask_facts pOut a).1, pOut.val.property.2⟩⟩,
    (oneZero_mask_facts pOut a).2⟩

/-- Change only the inactive input mask; original residual pair is unchanged. -/
def singleInput (pIn : SelectedSupport 2 4) (t : InputUniformPositions pIn) : SelectedSupport 2 3 :=
  ⟨⟨(pIn.val.val.1, singletonMask t.val.val), ⟨by
    intro i hi hj
    have he := (singletonMask_bit _ _).mp hi
    subst i
    exact t.val.property hj, pIn.val.property.2⟩⟩, by rw [singletonMask_size]; decide⟩
end AESConcrete.TwoOmittedTwoInputSource
