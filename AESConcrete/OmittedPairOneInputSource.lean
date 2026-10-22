import AESConcrete.OmittedPairOneInputRawFullEnergy
import AESConcrete.WeightedResidualLineCaps
import AESConcrete.TripleResponse

/-!
Lemmas for (10,9). The source is the original multiUniform: one input zero,
one input uniform, and one arbitrary signed joint residual h, including its
zero-pair value. The exact input split and outer output split use this SAME
source and h. Constructive fixed AES10/14/16 only.

No physical cap is asserted here.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedPairOneInputSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedPairOneInputRawGeometry
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform zeroUnit)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

abbrev normalizedSource (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  WeightedResidualLineCaps.normalizedSource pIn h

abbrev uniformWeight (pIn : SelectedSupport 2 3) :=
  WeightedResidualLineCaps.uniformWeight pIn

theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h =
      MultiUniformExpansion.multiUniform pIn.val.val.2 pIn.val.val.1 h := rfl

theorem normalizedSource_energy (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ r, h r ^ 2 :=
  WeightedResidualLineCaps.normalizedSource_energy pIn h

def inputUniform (pIn : SelectedSupport 2 3) : SourceUniformPositions pIn :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num))

def uniformIndexEquiv (pIn : SelectedSupport 2 3) : SourceUniformPositions pIn ≃ Fin 1 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card, Fintype.card_fin])

theorem uniform_unique (pIn : SelectedSupport 2 3) (u : SourceUniformPositions pIn) :
    u = inputUniform pIn := by
  apply (uniformIndexEquiv pIn).injective
  exact Subsingleton.elim _ _

theorem uniformWeight_eq_one (pIn : SelectedSupport 2 3) (x : AES.WordState) :
    uniformWeight pIn x = nonzeroUniform (x (inputUniform pIn).val.val) := by
  unfold uniformWeight WeightedResidualLineCaps.uniformWeight
  have he := (uniformIndexEquiv pIn).symm.prod_comp
    (fun u : SourceUniformPositions pIn => nonzeroUniform (x u.val.val))
  rw [Fin.prod_univ_one] at he
  rw [← he]
  rw [uniform_unique pIn ((uniformIndexEquiv pIn).symm 0)]

theorem normalizedSource_on_code (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) :
    normalizedSource pIn h c.val = h (residualTuple pOut pIn c) *
      nonzeroUniform (c.val (inputUniform pIn).val.val) := by
  change WeightedResidualLineCaps.normalizedSource pIn h c.val = _
  rw [WeightedResidualLineCaps.normalizedSource_eq]
  have hp : (∏ i : MultiUniformExpansion.InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (c.val i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [zeroUnit, supportConstant, identityKernel, c.property.2 i.val.val i.property]
  rw [hp, mul_one]
  change h (residualTuple pOut pIn c) * uniformWeight pIn c.val = _
  rw [uniformWeight_eq_one]

def bareKernel (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0
    (y i) (curve pOut pIn c i)

def rawResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn)

theorem rawResponse_eq_rawFullResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    rawResponse pOut pIn h = OmittedPairOneInputRawFullEnergy.rawFullResponse pOut pIn h := rfl

def inputZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn) (fun c => c.val (inputUniform pIn).val.val)

/-- W contains the original input U and no omitted output U. -/
def inputWeightedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val * bareKernel pOut pIn y c

private theorem one_uniform_summand (v : AES.Word) (a : ℝ) :
    a * nonzeroUniform v =
      (a - (if v = 0 then a else 0)) / Real.sqrt (q - 1) := by
  unfold nonzeroUniform
  rw [word_card_real]
  by_cases hv : v = 0 <;>
    simp [supportConstant, identityKernel, hv, div_eq_mul_inv]
    <;> ring

/-- Exact W=(A_empty-A_u)/sqrt D; no centering or h(0)=0. -/
theorem inputWeightedResponse_eq_split (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y - inputZeroResponse pOut pIn h y) / Real.sqrt (q - 1) := by
  funext y
  unfold inputWeightedResponse rawResponse inputZeroResponse
    WeightedResponse.rawResponse WeightedResponse.zeroResponse
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [normalizedSource_on_code]
  calc
    _ = (h (residualTuple pOut pIn c) * bareKernel pOut pIn y c) *
        nonzeroUniform (c.val (inputUniform pIn).val.val) := by ring
    _ = _ := one_uniform_summand _ _

/-- The two omitted physical output labels; both are active uniforms. -/
abbrev Omitted (pOut : SelectedSupport 2 4) :=
  GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1

theorem omitted_card (pOut : SelectedSupport 2 4) : Fintype.card (Omitted pOut) = 2 := by
  change Fintype.card {i : Fin 4 // ¬ maskBit pOut.val.val.1 i = true} = 2
  rw [Fintype.card_subtype_compl, maskCoordinates_card, retainedMask_size]
  decide

def omittedIndexEquiv (pOut : SelectedSupport 2 4) : Omitted pOut ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [omitted_card, Fintype.card_fin])

def omittedFirst (pOut : SelectedSupport 2 4) : Omitted pOut := (omittedIndexEquiv pOut).symm 0
def omittedSecond (pOut : SelectedSupport 2 4) : Omitted pOut := (omittedIndexEquiv pOut).symm 1

theorem omittedFirst_ne_second (pOut : SelectedSupport 2 4) :
    omittedFirst pOut ≠ omittedSecond pOut := by
  intro he
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [omittedFirst, omittedSecond, Equiv.apply_symm_apply] using
      congrArg (omittedIndexEquiv pOut) he
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def outputValue (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (c : Code pOut pIn) : AES.Word :=
  WordCrossZero.wordMixAddEquiv c.val a.val

/-- Every output restriction preserves normalizedSource, hence the same h. -/
def outputZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (fun c : Code pOut pIn => normalizedSource pIn h c.val)
    (bareKernel pOut pIn) (outputValue pOut pIn a)

def outputIntersectionResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse
    (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn)
    (outputValue pOut pIn (omittedFirst pOut))
    (outputValue pOut pIn (omittedSecond pOut))

def omittedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.weightedResponse
    (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn)
    (outputValue pOut pIn (omittedFirst pOut))
    (outputValue pOut pIn (omittedSecond pOut))

/-- Exact outer signed inclusion-exclusion; the +Wab term is retained. -/
theorem omittedResponse_eq_four (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        outputZeroResponse pOut pIn (omittedFirst pOut) h y -
        outputZeroResponse pOut pIn (omittedSecond pOut) h y +
        outputIntersectionResponse pOut pIn h y) / (q - 1) := by
  unfold omittedResponse
  rw [TripleResponse.weightedResponse_eq_four,
    TripleResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one), word_card_real]
  rfl
end AESConcrete.OmittedPairOneInputSource
