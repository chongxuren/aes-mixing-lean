import AESConcrete.TwoOmittedThreeInputEvents
import AESConcrete.TwoOmittedThreeInputScalar

/-!
# Eight-term original-input identity and retained triple-line norm

The unconditional eight-term expansion is used. The bare and three singleton
terms cancel; three Fourier planes and the signed ordinary graph line remain.
The original signed tuple h, including h(0), is shared by all eight terms. The
included raw modules supply their proofs; no (10,6) weighted endpoint is a
premise. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedThreeInputResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedThreeInputGeometry
open AESConcrete.TwoOmittedThreeInputEvents
open AESConcrete.TwoOmittedThreeInputScalar
open AESConcrete.ActivityCodeScalar (s s_pos)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

abbrev uniformFirst := OmittedUniformTwoOutputResponseEnergy.uniformFirst
abbrev uniformSecond := OmittedUniformTwoOutputResponseEnergy.uniformSecond
abbrev uniformThird := OmittedUniformTwoOutputResponseEnergy.uniformThird

theorem uniformFirst_ne_second (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformSecond pIn :=
  OmittedUniformTwoOutputResponseEnergy.uniformFirst_ne_second pIn

theorem uniformFirst_ne_third (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformThird pIn :=
  OmittedUniformTwoOutputResponseEnergy.uniformFirst_ne_third pIn

theorem uniformSecond_ne_third (pIn : SelectedSupport 1 4) :
    uniformSecond pIn ≠ uniformThird pIn :=
  OmittedUniformTwoOutputResponseEnergy.uniformSecond_ne_third pIn

def inputWeightedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ x : AES.WordState, normalizedSource pIn h x * stateKernel pOut y x

theorem inputWeightedResponse_eq_weighted (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = WeightedResponse.weightedResponse
      (fun x => h (residualTuple pIn x)) (stateKernel pOut)
      (fun x => x (uniformFirst pIn).val.val) (fun x => x (uniformSecond pIn).val.val)
      (fun x => x (uniformThird pIn).val.val) := by
  funext y
  unfold inputWeightedResponse WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro x _
  -- Unfold the local abbrev before the provider definition's summand.
  simp only [TwoOmittedThreeInputGeometry.normalizedSource,
    OmittedUniformTwoOutputSplit.normalizedSource]
  rw [OmittedUniformTwoOutputResponseEnergy.uniform_product]
  unfold residualTuple
  ring

/-- Every event exists before any cancellation is used. -/
theorem inputWeightedResponse_eq_eight (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (bareResponse pOut pIn h y - singleResponse pOut pIn (uniformFirst pIn) h y -
        singleResponse pOut pIn (uniformSecond pIn) h y -
        singleResponse pOut pIn (uniformThird pIn) h y +
        pairResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) h y +
        pairResponse pOut pIn (uniformFirst pIn) (uniformThird pIn) h y +
        pairResponse pOut pIn (uniformSecond pIn) (uniformThird pIn) h y -
        tripleResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) (uniformThird pIn) h y) /
          inputNormalizer := by
  rw [inputWeightedResponse_eq_weighted, TwoOutputThreeUniformCaps.weightedResponse_eq_eight]
  rfl

/-- The triple intersection line is retained with its negative sign. -/
theorem inputWeightedResponse_eq_four (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (pairResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) h y +
        pairResponse pOut pIn (uniformFirst pIn) (uniformThird pIn) h y +
        pairResponse pOut pIn (uniformSecond pIn) (uniformThird pIn) h y -
        tripleResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) (uniformThird pIn) h y) /
          inputNormalizer := by
  rw [inputWeightedResponse_eq_eight, bareResponse_eq_zero,
    singleResponse_eq_zero, singleResponse_eq_zero, singleResponse_eq_zero]
  simp only [Pi.zero_apply, sub_self, sub_zero, zero_add]

/-- Add three plane norms s*a and one line norm a before squaring. -/
theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (rawNormNumerator / inputNormalizer) ^ 2 * ∑ r, h r ^ 2 := by
  have hp (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
      (∑ y, pairResponse pOut pIn u v h y ^ 2) ≤
        (s * normBase) ^ 2 * ∑ r, h r ^ 2 := by
    rw [planeNorm_sq]
    exact pairResponse_energy pOut pIn u v huv h
  have ht : (∑ y, tripleResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn)
      (uniformThird pIn) h y ^ 2) ≤ normBase ^ 2 * ∑ r, h r ^ 2 := by
    rw [normBase_sq]
    exact tripleResponse_energy pOut pIn _ _ _ (uniformFirst_ne_second pIn)
      (uniformFirst_ne_third pIn) (uniformSecond_ne_third pIn) h
  have hp02 : (∑ y, (-pairResponse pOut pIn (uniformFirst pIn) (uniformThird pIn) h y) ^ 2) ≤
      (s * normBase) ^ 2 * ∑ r, h r ^ 2 := by
    simpa only [neg_sq] using hp _ _ (uniformFirst_ne_third pIn)
  have hp12 : (∑ y, (-pairResponse pOut pIn (uniformSecond pIn) (uniformThird pIn) h y) ^ 2) ≤
      (s * normBase) ^ 2 * ∑ r, h r ^ 2 := by
    simpa only [neg_sq] using hp _ _ (uniformSecond_ne_third pIn)
  have ha : 0 ≤ s * normBase := mul_nonneg s_pos.le normBase_nonneg
  have hl := WeightedResponse.four_response_l2_le
    (pairResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) h)
    (fun y => -pairResponse pOut pIn (uniformFirst pIn) (uniformThird pIn) h y)
    (fun y => -pairResponse pOut pIn (uniformSecond pIn) (uniformThird pIn) h y)
    (tripleResponse pOut pIn (uniformFirst pIn) (uniformSecond pIn) (uniformThird pIn) h)
    h (s * normBase) (s * normBase) (s * normBase) normBase inputNormalizer
    ha ha ha normBase_nonneg (hp _ _ (uniformFirst_ne_second pIn)) hp02 hp12 ht
  simp only [sub_neg_eq_add, abs_of_nonneg inputNormalizer_nonneg] at hl
  rw [← inputWeightedResponse_eq_four] at hl
  have hn : s * normBase + s * normBase + s * normBase + normBase = rawNormNumerator := by
    unfold rawNormNumerator
    ring
  rw [hn] at hl
  have hc : 0 ≤ rawNormNumerator / inputNormalizer :=
    div_nonneg rawNormNumerator_nonneg inputNormalizer_nonneg
  have hs := (sq_le_sq₀ (l2_nonneg (inputWeightedResponse pOut pIn h))
    (mul_nonneg hc (l2_nonneg h))).mpr hl
  simpa only [mul_pow, l2_sq] using hs

end AESConcrete.TwoOmittedThreeInputResponse
