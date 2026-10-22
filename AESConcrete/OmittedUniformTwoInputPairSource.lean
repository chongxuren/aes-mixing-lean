import AESConcrete.OmittedUniformTwoInputRawFullEnergy
import AESConcrete.MultiUniformExpansion
import AESConcrete.TripleResponse

/-!
# Exact original normalized joint source for proposed (9,10)

The imported raw geometry and energy modules are used through their
definitions only.

The input has two ORIGINAL residual labels and two ORIGINAL nonzero-uniform
labels. One arbitrary signed JOINT h is retained, including its zero-pair
value. The normalized source has exactly the original h counting energy. Its
exact two-uniform expansion is A-B-C+D, with denominator q-1; D is retained.
No quantitative response estimate, desired-bound premise, selected-minor bound
or physical aggregation is supplied here.

Constructive fixed AES10/14/16; independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoInputPairSource
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)
open AESConcrete.MultiUniformExpansion (multiUniform normalizedLeg InactivePositions)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

/-- The original inactive and residual masks are passed to multiUniform unchanged. -/
def normalizedSource (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  multiUniform pIn.val.val.2 pIn.val.val.1 h

/-- Explicit source interface for later selected-piece transfer; no new h is chosen. -/
theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h =
      MultiUniformExpansion.multiUniform pIn.val.val.2 pIn.val.val.1 h := rfl

theorem normalizedSource_energy (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 :=
  MultiUniformExpansion.multiUniform_energy AES.word_card_gt_one _ _ h

/-- Only the two actual original input uniform positions occur in this weight. -/
def uniformWeight (pIn : SelectedSupport 2 4) (x : AES.WordState) : ℝ :=
  ∏ j : SourceUniformPositions pIn, nonzeroUniform (x j.val.val)

private theorem normalizedSource_eq_with_inactive (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    normalizedSource pIn h x = h (fun i => x i.val) *
      (∏ i : InactivePositions pIn.val.val.2 pIn.val.val.1,
        zeroUnit (x i.val.val)) * uniformWeight pIn x := by
  unfold normalizedSource multiUniform coordinateEmbedding uniformWeight
  rw [counting_prod_instances (X := OtherCoordinates pIn.val.val.1) _ inferInstance]
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : OtherCoordinates pIn.val.val.1 => maskBit pIn.val.val.2 i.val = true)]
  have hI (i : InactivePositions pIn.val.val.2 pIn.val.val.1) :
      normalizedLeg (maskBit pIn.val.val.2 i.val.val) (x i.val.val) =
        zeroUnit (x i.val.val) := by
    simp [normalizedLeg, i.property]
  have hU (i : SourceUniformPositions pIn) :
      normalizedLeg (maskBit pIn.val.val.2 i.val.val) (x i.val.val) =
        nonzeroUniform (x i.val.val) := by
    simp [normalizedLeg, i.property]
  simp_rw [hI, hU]
  ring

/-- The input inactive mask is empty; the same original joint h remains. -/
theorem normalizedSource_eq (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    normalizedSource pIn h x = h (fun i => x i.val) * uniformWeight pIn x := by
  rw [normalizedSource_eq_with_inactive]
  have hp : (∏ i : InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (x i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact (input_inactive_not pIn i.val.val i.property).elim
  rw [hp, mul_one]

theorem normalizedSource_on_code (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) :
    normalizedSource pIn h c.val =
      h (residualTuple pOut pIn c) * uniformWeight pIn c.val :=
  normalizedSource_eq pIn h c.val

/-- This only names the two physical positions; it does not factor h. -/
def uniformIndexEquiv (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card, Fintype.card_fin])

def uniformFirst (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

theorem uniformFirst_ne_second (pIn : SelectedSupport 2 4) :
    uniformFirst pIn ≠ uniformSecond pIn := by
  intro he
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [uniformFirst, uniformSecond, Equiv.apply_symm_apply] using
      congrArg (uniformIndexEquiv pIn) he
  exact (by decide : (0 : Fin 2) ≠ 1) h01

theorem uniformWeight_eq_two (pIn : SelectedSupport 2 4) (x : AES.WordState) :
    uniformWeight pIn x =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) := by
  have he := (uniformIndexEquiv pIn).symm.prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (x j.val.val))
  simpa only [Fin.prod_univ_two, uniformFirst, uniformSecond, uniformWeight] using he.symm

/-- The actual two retained residual-kernel entries, with counting measure. -/
def bareKernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn c i)

def rawResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn)

theorem rawResponse_eq_rawFullResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    rawResponse pOut pIn h =
      OmittedUniformTwoInputRawFullEnergy.rawFullResponse pOut pIn h := rfl

/-- The actual original input-zero event at u, on the original full code. -/
def zeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.zeroResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn) (fun c => c.val u.val.val)

/-- Retain the intersection of both original input-zero events. -/
def intersectionResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u v : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  TripleResponse.intersectionResponse
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val)

/-- W contains both original normalized input uniforms and no output uniform. -/
def inputWeightedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val * bareKernel pOut pIn y c

theorem inputWeightedResponse_eq_two (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = TripleResponse.weightedResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) := by
  funext y
  unfold inputWeightedResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [normalizedSource_on_code, uniformWeight_eq_two]
  ring

/-- Exact W=(A-B-C+D)/(q-1); the signed intersection D is not discarded. -/
theorem inputWeightedResponse_eq_four (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y - zeroResponse pOut pIn (uniformFirst pIn) h y -
        zeroResponse pOut pIn (uniformSecond pIn) h y +
        intersectionResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) h y) /
          (ActivityCodeScalar.q - 1) := by
  rw [inputWeightedResponse_eq_two, TripleResponse.weightedResponse_eq_four]
  have hn := TripleResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one)
  rw [DoubleUniformFourierEnergy.word_card_real] at hn
  simp only [hn, rawResponse, zeroResponse, intersectionResponse]

end AESConcrete.OmittedUniformTwoInputPairSource
