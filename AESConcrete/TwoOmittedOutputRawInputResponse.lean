import AESConcrete.TwoOmittedOutputRawInputEventEnergy
import AESConcrete.WeightedResidualLineCaps
import AESConcrete.TripleResponse

/-!
# Exact original-two-uniform raw response for proposed (10,6)

Output support is (2,4), input support is (1,3). W retains the original input-
zero delta and the two original normalized nonzero uniforms, with no omitted-
output weight yet. Every term uses the same arbitrary signed original residual
tuple h, including h(0). Its exact split is (A-B-C+F)/(q-1): A vanishes by
proved raw cancellation, B,C are planes, and F remains a line. No event
energy, injectivity, centering or desired response bound is assumed as a
theorem premise.

The full selected-minor response, output inclusion-exclusion, physical
factor72 and certificate comparison are outside this bounded packet.
Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputRawInputResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry
open AESConcrete.TwoOmittedOutputRawResponse (bareKernel bareResponse)
open AESConcrete.TwoOmittedOutputRawInputEvents
open AESConcrete.TwoOmittedOutputRawInputEventEnergy
open AESConcrete.NonzeroUniformGraphCap (zeroUnit nonzeroUniform)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s s_pos s_sq q_sub_one_pos)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def uniformIndexEquiv (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 1 3) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

theorem uniformFirst_ne_second (pIn : SelectedSupport 1 3) :
    uniformFirst pIn ≠ uniformSecond pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

/-- The accepted source is exactly multiUniform Z J h, including original Z. -/
def normalizedSource (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  WeightedResidualLineCaps.normalizedSource pIn h

theorem normalizedSource_eq_multiUniform (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h =
      MultiUniformExpansion.multiUniform pIn.val.val.2 pIn.val.val.1 h := rfl

theorem normalizedSource_energy (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 :=
  WeightedResidualLineCaps.normalizedSource_energy pIn h

theorem normalizedSource_on_code (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) :
    normalizedSource pIn h c.val = h (residualTuple pOut pIn c) *
      WeightedResidualLineCaps.uniformWeight pIn c.val := by
  rw [normalizedSource, WeightedResidualLineCaps.normalizedSource_eq]
  have hp : (∏ i : MultiUniformExpansion.InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (c.val i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hz := c.property.2 i.val.val i.property
    simp [zeroUnit, supportConstant, identityKernel, hz]
  rw [hp, mul_one]
  rfl

theorem uniformWeight_eq_two (pIn : SelectedSupport 1 3) (x : AES.WordState) :
    WeightedResidualLineCaps.uniformWeight pIn x =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) := by
  have he := (uniformIndexEquiv pIn).symm.prod_comp
    (fun i : SourceUniformPositions pIn => nonzeroUniform (x i.val.val))
  simpa only [Fin.prod_univ_two, uniformFirst, uniformSecond,
    WeightedResidualLineCaps.uniformWeight] using he.symm

/-- A: bare response before the two original input uniforms. -/
def rawResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn)

theorem rawResponse_eq_zero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) : rawResponse pOut pIn h = 0 :=
  TwoOmittedOutputRawResponse.bareResponse_eq_zero pOut pIn h

/-- W has the original inactive delta and precisely the original two uniforms. -/
def inputWeightedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val * bareKernel pOut pIn y c

theorem inputWeightedResponse_eq_two (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
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

/-- Exact A-B-C+F identity; the actual intersection line F is retained. -/
theorem inputWeightedResponse_eq_four (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y -
        eventResponse pOut pIn (singleMask (uniformFirst pIn)) h y -
        eventResponse pOut pIn (singleMask (uniformSecond pIn)) h y +
        eventResponse pOut pIn (doubleMask (uniformFirst pIn) (uniformSecond pIn)) h y) /
          (q - 1) := by
  rw [inputWeightedResponse_eq_two, TripleResponse.weightedResponse_eq_four]
  have hn := TripleResponse.normalizer_eq AES.Word AES.word_card_gt_one.le
  rw [word_card_real] at hn
  simp only [hn, single_zeroResponse_eq, double_intersectionResponse_eq, rawResponse]

def normBase : ℝ := rho * Real.sqrt kappa

theorem normBase_nonneg : 0 ≤ normBase :=
  mul_nonneg rho_nonneg (Real.sqrt_nonneg _)

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa := by
  unfold normBase
  rw [mul_pow, Real.sq_sqrt kappa_nonneg]

theorem singleNorm_sq : (s * normBase) ^ 2 = q * rho ^ 2 * kappa := by
  rw [mul_pow, s_sq, normBase_sq]
  ring

/-- Only W: no output uniform, selected-minor or physical-block assertion. -/
theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (((2 * s + 1) * rho * Real.sqrt kappa) / (q - 1)) ^ 2 * ∑ x, h x ^ 2 := by
  have hfull : (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) y ^ 2) ≤ (0 : ℝ) ^ 2 * ∑ x, h x ^ 2 := by
    change (∑ y, rawResponse pOut pIn h y ^ 2) ≤ _
    rw [rawResponse_eq_zero]
    simp
  have hsingle (u : SourceUniformPositions pIn) :
      (∑ y, WeightedResponse.zeroResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
        (bareKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
          (s * normBase) ^ 2 * ∑ x, h x ^ 2 := by
    rw [singleNorm_sq]
    exact single_zeroResponse_energy pOut pIn u h
  have hdouble : (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
        normBase ^ 2 * ∑ x, h x ^ 2 := by
    rw [normBase_sq]
    exact double_intersectionResponse_energy pOut pIn
      (uniformFirst pIn) (uniformSecond pIn) (uniformFirst_ne_second pIn) h
  have he := TripleResponse.weightedResponse_energy_le AES.word_card_gt_one.le
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val) h
    0 (s * normBase) (s * normBase) normBase (by norm_num)
    (mul_nonneg s_pos.le normBase_nonneg) (mul_nonneg s_pos.le normBase_nonneg)
    normBase_nonneg hfull (hsingle _) (hsingle _) hdouble
  rw [← inputWeightedResponse_eq_two, word_card_real] at he
  calc
    _ ≤ ((0 + s * normBase + s * normBase + normBase) ^ 2 / (q - 1) ^ 2) *
        ∑ x, h x ^ 2 := he
    _ = _ := by rw [div_pow]; unfold normBase; ring

end AESConcrete.TwoOmittedOutputRawInputResponse
