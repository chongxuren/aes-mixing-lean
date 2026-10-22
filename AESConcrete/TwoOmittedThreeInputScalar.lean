--
--
import AESConcrete.OmittedUniformTwoOutputScalar
import AESConcrete.WeightedResponse

/-!
# (10,7) scalar arithmetic, separate from all response estimates

The strict certificate comparison is scalar only. Physical factor24 is
justified in StepCaps, never assumed here as an analytic result. Constructive
fixed AES10/14/16.
-/

noncomputable section
namespace AESConcrete.TwoOmittedThreeInputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def normBase : ℝ := rho * Real.sqrt kappa
def inputNormalizer : ℝ := WeightedResponse.normalizer AESMixing.AES.Word
def rawNormNumerator : ℝ := (3 * s + 1) * normBase
def oneZeroNormNumerator : ℝ := (3 * s + 3) * normBase
def twoZeroNormNumerator : ℝ := (s + 3) * normBase
def C : ℝ := rho ^ 2 * kappa * (10 * s + 10) ^ 2 / (q - 1) ^ 5

theorem normBase_nonneg : 0 ≤ normBase :=
  mul_nonneg rho_nonneg (Real.sqrt_nonneg _)

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa := by
  unfold normBase
  rw [mul_pow, Real.sq_sqrt kappa_nonneg]

theorem planeNorm_sq : (s * normBase) ^ 2 = q * rho ^ 2 * kappa := by
  rw [mul_pow, s_sq, normBase_sq]
  ring

theorem inputNormalizer_pos : 0 < inputNormalizer :=
  WeightedResponse.normalizer_pos AESMixing.AES.Word (by rw [AESMixing.AES.word_card]; norm_num)

theorem inputNormalizer_nonneg : 0 ≤ inputNormalizer := inputNormalizer_pos.le

theorem inputNormalizer_sq : inputNormalizer ^ 2 = (q - 1) ^ 3 := by
  rw [inputNormalizer, WeightedResponse.normalizer_sq AESMixing.AES.Word
    (by rw [AESMixing.AES.word_card]; norm_num), AESMixing.AES.word_card]
  rfl

theorem rawNormNumerator_nonneg : 0 ≤ rawNormNumerator :=
  mul_nonneg (by linarith [s_pos]) normBase_nonneg

theorem oneZeroNormNumerator_nonneg : 0 ≤ oneZeroNormNumerator :=
  mul_nonneg (by linarith [s_pos]) normBase_nonneg

theorem twoZeroNormNumerator_nonneg : 0 ≤ twoZeroNormNumerator :=
  mul_nonneg (by linarith [s_pos]) normBase_nonneg

theorem C_nonneg : 0 ≤ C :=
  div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg _))
    (pow_nonneg q_sub_one_pos.le _)

theorem oneZero_coefficient_eq :
    (oneZeroNormNumerator / inputNormalizer) ^ 2 = OmittedUniformTwoOutputScalar.weightedC := by
  rw [div_pow, inputNormalizer_sq]
  rfl

theorem twoZero_coefficient_eq :
    (twoZeroNormNumerator / inputNormalizer) ^ 2 =
      rho ^ 2 * kappa * (s + 3) ^ 2 / (q - 1) ^ 3 := by
  rw [div_pow, inputNormalizer_sq]
  unfold twoZeroNormNumerator
  rw [mul_pow, normBase_sq]
  ring

theorem numerator_sum :
    rawNormNumerator + oneZeroNormNumerator + oneZeroNormNumerator + twoZeroNormNumerator =
      (10 * s + 10) * normBase := by
  unfold rawNormNumerator oneZeroNormNumerator twoZeroNormNumerator
  ring

/-- Three input uniform legs contribute D³ in energy. The two original
omitted output legs contribute D², for total D⁵. -/
theorem normalized_four_coefficient_eq :
    ((rawNormNumerator / inputNormalizer + oneZeroNormNumerator / inputNormalizer +
      oneZeroNormNumerator / inputNormalizer + twoZeroNormNumerator / inputNormalizer) /
        (q - 1)) ^ 2 = C := by
  have hh : rawNormNumerator / inputNormalizer + oneZeroNormNumerator / inputNormalizer +
      oneZeroNormNumerator / inputNormalizer + twoZeroNormNumerator / inputNormalizer =
      (rawNormNumerator + oneZeroNormNumerator + oneZeroNormNumerator + twoZeroNormNumerator) /
        inputNormalizer := by ring
  rw [hh, numerator_sum, div_div]
  simp only [div_pow, mul_pow, inputNormalizer_sq, normBase_sq]
  have hd : (q - 1) ^ 3 * (q - 1) ^ 2 = (q - 1) ^ 5 := by ring
  rw [hd]
  unfold C
  ring

theorem certificate_10_7_entry :
    L (10 : Fin 14) (7 : Fin 14) =
      (510308631501521 : ℝ) / 77056884765625000000000000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 10 7 := by
  rw [certificate_10_7_entry]
  norm_num [AESRound.Terminal.lambda]

-- This exact-rational tactic is SOURCE TEXT, not an executed certificate.
theorem certificate_strict_bound : 24 * C < (lambda * L 10 7) ^ 2 := by
  rw [certificate_10_7_entry]
  norm_num [C, rho, kappa, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 10 7 ∧ 24 * C ≤ (lambda * L 10 7) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.TwoOmittedThreeInputScalar
