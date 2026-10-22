import AESConcrete.OmittedUniformTwoInputPairScalar
import AESConcrete.OmittedUniformPairEventEnergy
import AESConcrete.OmittedUniformPairZeroPlane
import AESConcrete.OmittedUniformTwoResponseEnergy

/-!
# actual (9,10) response-energy composition

The same arbitrary signed original joint h, including zero, is used in the raw
response, both singleton exclusions, their intersection and the extra-output-
zero response. Norms add before squaring. Two input uniforms contribute q-1;
the omitted output contributes sqrt(q-1). This module supplies no physical
support factor. Constructive fixed AES10/14/16, independent uniform retained
keys, whitening, omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputPairResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.OmittedUniformTwoInputPairSource
open AESConcrete.OmittedUniformTwoInputPairSplit (extraZeroResponse actualResponse)
open AESConcrete.OmittedUniformTwoInputPairScalar
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem rawResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤ fullRawNorm ^ 2 * ∑ u, h u ^ 2 := by
  rw [rawResponse_eq_rawFullResponse]
  exact (OmittedUniformTwoInputRawFullEnergy.rawFullResponse_energy pOut pIn h).trans
    (mul_le_mul_of_nonneg_right full_energy_coefficient_le
      (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

theorem zeroResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, zeroResponse pOut pIn u h y ^ 2) ≤ eventRawNorm ^ 2 * ∑ v, h v ^ 2 := by
  rw [← single_energy_coefficient_eq]
  exact OmittedUniformPairEventEnergy.single_zeroResponse_energy pOut pIn u h

theorem intersectionResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, intersectionResponse pOut pIn u v h y ^ 2) ≤
      eventRawNorm ^ 2 * ∑ z, h z ^ 2 :=
  (OmittedUniformPairEventEnergy.double_intersectionResponse_energy
    pOut pIn u v huv h).trans
      (mul_le_mul_of_nonneg_right intersection_energy_coefficient_le
        (Finset.sum_nonneg (fun z _ => sq_nonneg (h z))))

/-- The three input-exclusion norms are charged against one original h. -/
theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (inputNorm / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  have hA : (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn) y ^ 2) ≤
      fullRawNorm ^ 2 * ∑ u, h u ^ 2 := rawResponse_energy pOut pIn h
  have hB : (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformFirst pIn).val.val) y ^ 2) ≤
      eventRawNorm ^ 2 * ∑ u, h u ^ 2 :=
    zeroResponse_energy pOut pIn (uniformFirst pIn) h
  have hC : (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
      eventRawNorm ^ 2 * ∑ u, h u ^ 2 :=
    zeroResponse_energy pOut pIn (uniformSecond pIn) h
  have hD : (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
      eventRawNorm ^ 2 * ∑ u, h u ^ 2 :=
    intersectionResponse_energy pOut pIn (uniformFirst pIn) (uniformSecond pIn)
      (uniformFirst_ne_second pIn) h
  have he := TripleResponse.weightedResponse_energy_le
    (le_of_lt AES.word_card_gt_one)
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
    (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val) h
    fullRawNorm eventRawNorm eventRawNorm eventRawNorm
    fullRawNorm_nonneg eventRawNorm_nonneg eventRawNorm_nonneg eventRawNorm_nonneg
    hA hB hC hD
  rw [← inputWeightedResponse_eq_two] at he
  simpa only [input_norm_numerator, word_card_real, div_pow] using he

/-- W0 retains both original normalized input uniforms on its actual plane. -/
theorem extraZeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, extraZeroResponse pOut pIn h y ^ 2) ≤
      (eventRawNorm / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  have he := OmittedUniformPairZeroPlane.extraZeroResponse_energy pOut pIn h
  rw [single_energy_coefficient_eq] at he
  exact he.trans_eq (by rw [div_pow]; ring)

/-- No quantitative desired-bound premise occurs in this actual response cap. -/
theorem actualResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  have he := OmittedUniformTwoResponseEnergy.sub_div_energy_le
    (inputWeightedResponse pOut pIn h) (extraZeroResponse pOut pIn h) h
    inputNorm eventRawNorm (q - 1) (Real.sqrt (q - 1))
    inputNorm_nonneg eventRawNorm_nonneg q_sub_one_pos.le (Real.sqrt_nonneg _)
    (inputWeightedResponse_energy pOut pIn h) (extraZeroResponse_energy pOut pIn h)
  have hd : (q - 1) ^ 2 * (Real.sqrt (q - 1)) ^ 2 = (q - 1) ^ 3 := by
    rw [Real.sq_sqrt q_sub_one_pos.le]
    ring
  rw [hd, split_coefficient_eq] at he
  rw [OmittedUniformTwoInputPairSplit.actualResponse_eq_split]
  -- The two definitionally equal retained tuples carry different counting instances.
  have counting_sum_instances {X : Type} (a b : Fintype X) (f : X → ℝ) :
      (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
    have h : a = b := Subsingleton.elim _ _
    cases h
    rfl
  calc
    _ = ∑ y : Retained pOut → AES.Word,
        ((inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
          Real.sqrt (q - 1)) ^ 2 := counting_sum_instances _ _ _
    _ ≤ _ := he

end AESConcrete.OmittedUniformTwoInputPairResponseEnergy
