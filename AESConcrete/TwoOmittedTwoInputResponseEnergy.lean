import AESConcrete.TwoOmittedTwoInputOutputEnergy

/-!
Lemmas for (10,10). Two nested exact signed expansions preserve the same h and
original input U. The raw full term cancels by actual row sums; the surviving
input intersection is kept. Output norms are added before one final square,
with physical factor handled separately. Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedTwoInputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedTwoInputSource
open AESConcrete.TwoOmittedTwoInputScalar
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- W has norm (2q*rho*eta+rho^2)/D against the original h. -/
theorem inputWeightedResponse_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (inputNorm / (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  have hA : (∑ y, WeightedResponse.rawResponse
      (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut) y ^ 2) ≤
      (0 : ℝ) ^ 2 * ∑ r, h r ^ 2 := by
    change (∑ y, rawResponse pOut pIn h y ^ 2) ≤ _
    rw [TwoOmittedTwoInputInputEnergy.rawResponse_eq_zero]
    simp
  have hB : (∑ y, WeightedResponse.zeroResponse
      (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)
      (fun x => x (uniformFirst pIn).val.val) y ^ 2) ≤ fullRawNorm ^ 2 * ∑ r, h r ^ 2 :=
    TwoOmittedTwoInputInputEnergy.inputZero_energy pOut pIn _ h
  have hC : (∑ y, WeightedResponse.zeroResponse
      (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)
      (fun x => x (uniformSecond pIn).val.val) y ^ 2) ≤ fullRawNorm ^ 2 * ∑ r, h r ^ 2 :=
    TwoOmittedTwoInputInputEnergy.inputZero_energy pOut pIn _ h
  have hD : (∑ y, TripleResponse.intersectionResponse
      (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)
      (fun x => x (uniformFirst pIn).val.val) (fun x => x (uniformSecond pIn).val.val) y ^ 2) ≤
      eventRawNorm ^ 2 * ∑ r, h r ^ 2 := TwoOmittedTwoInputInputEnergy.inputIntersection_energy pOut pIn h
  have he := TripleResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun x : AES.WordState => h (fun i => x i.val)) (bareKernel pOut)
    (fun x => x (uniformFirst pIn).val.val) (fun x => x (uniformSecond pIn).val.val) h
    0 fullRawNorm fullRawNorm eventRawNorm (by norm_num)
    fullRawNorm_nonneg fullRawNorm_nonneg eventRawNorm_nonneg hA hB hC hD
  rw [← inputWeightedResponse_eq_two] at he
  simpa only [input_coefficient_eq, word_card_real, div_pow] using he

/-- R has coefficient C=(4q*rho*eta+8rho^2)^2/D^4 without an endpoint premise. -/
theorem omittedResponse_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, omittedResponse pOut pIn h y ^ 2) ≤ C * ∑ r, h r ^ 2 := by
  have ha := div_nonneg inputNorm_nonneg q_sub_one_pos.le
  have hb := div_nonneg outputSingleNorm_nonneg q_sub_one_pos.le
  have hd := div_nonneg eventRawNorm_nonneg q_sub_one_pos.le
  have he := TripleResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (normalizedSource pIn h) (bareKernel pOut)
    (outputValue pOut (omittedFirst pOut)) (outputValue pOut (omittedSecond pOut)) h
    (inputNorm / (q - 1)) (outputSingleNorm / (q - 1))
    (outputSingleNorm / (q - 1)) (eventRawNorm / (q - 1)) ha hb hb hd
    (inputWeightedResponse_energy pOut pIn h)
    (TwoOmittedTwoInputOutputEnergy.outputZero_energy pOut pIn _ h)
    (TwoOmittedTwoInputOutputEnergy.outputZero_energy pOut pIn _ h)
    (TwoOmittedTwoInputOutputEnergy.outputIntersection_energy pOut pIn h)
  rw [word_card_real, outer_coefficient_eq] at he
  exact he
end AESConcrete.TwoOmittedTwoInputResponseEnergy
