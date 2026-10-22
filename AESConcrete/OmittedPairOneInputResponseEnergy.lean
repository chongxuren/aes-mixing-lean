import AESConcrete.OmittedPairOneInputEvents
import AESConcrete.OmittedPairOneInputScalar
import AESConcrete.OmittedPairOneInputNorm

/-!
Lemmas for (10,9). All four output terms use the original normalizedSource and
original signed h. Input normalization is charged once as sqrt D. Output
normalization is charged once as D. Triangle inequalities precede squaring.
Constructive fixed AES10/14/16 only.

No desired-bound premise or physical support count is assumed.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedPairOneInputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedPairOneInputRawGeometry
open AESConcrete.OmittedPairOneInputSource
open AESConcrete.OmittedPairOneInputScalar
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem rawResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤ fullRawNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [rawResponse_eq_rawFullResponse]
  exact (OmittedPairOneInputRawFullEnergy.rawFullResponse_energy pOut pIn h).trans
    (mul_le_mul_of_nonneg_right full_energy_coefficient_le
      (Finset.sum_nonneg (fun r _ => sq_nonneg (h r))))

theorem inputZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputZeroResponse pOut pIn h y ^ 2) ≤ eventRawNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [← single_energy_coefficient_eq]
  exact OmittedPairOneInputEvents.input_zero_response_energy pOut pIn h

/-- The sole original input U is expanded before its norm is bounded. -/
theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (inputNorm / Real.sqrt (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  have hA : (∑ y, rawResponse pOut pIn h y ^ 2) ≤
      (fullRawNorm / 1) ^ 2 * ∑ r, h r ^ 2 := by simpa using rawResponse_energy pOut pIn h
  have hB : (∑ y, inputZeroResponse pOut pIn h y ^ 2) ≤
      (eventRawNorm / 1) ^ 2 * ∑ r, h r ^ 2 := by simpa using inputZeroResponse_energy pOut pIn h
  have he := OmittedPairOneInputNorm.sub_div_energy_le
    (rawResponse pOut pIn h) (inputZeroResponse pOut pIn h) h
    fullRawNorm eventRawNorm 1 (Real.sqrt (q - 1))
    fullRawNorm_nonneg eventRawNorm_nonneg (by norm_num) (Real.sqrt_nonneg _) hA hB
  rw [inputWeightedResponse_eq_split]
  simpa only [one_pow, one_mul, input_norm_numerator, div_pow] using he

theorem outputZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputZeroResponse pOut pIn a h y ^ 2) ≤
      (eventRawNorm / Real.sqrt (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  have he := OmittedPairOneInputEvents.single_output_response_energy pOut pIn a h
  rw [single_energy_coefficient_eq] at he
  simpa only [div_pow, Real.sq_sqrt q_sub_one_pos.le] using he

/-- The +Wab term is retained, with its original input U. -/
theorem outputIntersectionResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputIntersectionResponse pOut pIn h y ^ 2) ≤
      (eventRawNorm / Real.sqrt (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  have he := OmittedPairOneInputEvents.double_output_response_energy pOut pIn h
  have hc : rho ^ 2 * kappa / (q - 1) ≤
      (eventRawNorm / Real.sqrt (q - 1)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt q_sub_one_pos.le]
    exact div_le_div_of_nonneg_right intersection_energy_coefficient_le q_sub_one_pos.le
  exact he.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun r _ => sq_nonneg (h r))))

theorem outer_coefficient_eq :
    ((inputNorm / Real.sqrt (q - 1) + eventRawNorm / Real.sqrt (q - 1) +
      eventRawNorm / Real.sqrt (q - 1) + eventRawNorm / Real.sqrt (q - 1)) ^ 2 /
        (q - 1) ^ 2) = C := by
  have hd : q - 1 ≠ 0 := ne_of_gt q_sub_one_pos
  calc
    _ = ((inputNorm + 3 * eventRawNorm) / Real.sqrt (q - 1)) ^ 2 / (q - 1) ^ 2 := by
      congr 2 <;> ring
    _ = C := by
      rw [div_pow, Real.sq_sqrt q_sub_one_pos.le]
      unfold C numerator inputNorm
      field_simp [hd]
      <;> ring

/-- The complete proposed selected-response cap, with no quantitative premise. -/
theorem omittedResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, omittedResponse pOut pIn h y ^ 2) ≤ C * ∑ r, h r ^ 2 := by
  have hn : 0 ≤ inputNorm / Real.sqrt (q - 1) :=
    div_nonneg inputNorm_nonneg (Real.sqrt_nonneg _)
  have he : 0 ≤ eventRawNorm / Real.sqrt (q - 1) :=
    div_nonneg eventRawNorm_nonneg (Real.sqrt_nonneg _)
  have hb := TripleResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun c : Code pOut pIn => normalizedSource pIn h c.val) (bareKernel pOut pIn)
    (outputValue pOut pIn (omittedFirst pOut)) (outputValue pOut pIn (omittedSecond pOut)) h
    (inputNorm / Real.sqrt (q - 1)) (eventRawNorm / Real.sqrt (q - 1))
    (eventRawNorm / Real.sqrt (q - 1)) (eventRawNorm / Real.sqrt (q - 1))
    hn he he he (inputWeightedResponse_energy pOut pIn h)
    (outputZeroResponse_energy pOut pIn _ h) (outputZeroResponse_energy pOut pIn _ h)
    (outputIntersectionResponse_energy pOut pIn h)
  rw [word_card_real, outer_coefficient_eq] at hb
  exact hb
end AESConcrete.OmittedPairOneInputResponseEnergy
