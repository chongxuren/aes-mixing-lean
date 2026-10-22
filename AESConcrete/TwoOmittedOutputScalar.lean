import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# (10,6) coefficient and exact scalar certificate

These scalar proofs do not establish any analytic response bound or physical
step cap. Constructive fixed AES10/14/16, independent retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
namespace AESConcrete.TwoOmittedOutputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def normBase : ℝ := rho * Real.sqrt kappa
def rawNormNumerator : ℝ := (2 * s + 1) * normBase
def oneZeroNormNumerator : ℝ := (s + 2) * normBase
def C : ℝ := rho ^ 2 * kappa * (4 * s + 6) ^ 2 / (q - 1) ^ 4

theorem normBase_nonneg : 0 ≤ normBase :=
  mul_nonneg rho_nonneg (Real.sqrt_nonneg _)

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa := by
  unfold normBase
  rw [mul_pow, Real.sq_sqrt kappa_nonneg]

theorem rawNormNumerator_nonneg : 0 ≤ rawNormNumerator :=
  mul_nonneg (by linarith [s_pos]) normBase_nonneg

theorem oneZeroNormNumerator_nonneg : 0 ≤ oneZeroNormNumerator :=
  mul_nonneg (by linarith [s_pos]) normBase_nonneg

theorem C_nonneg : 0 ≤ C :=
  div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg _))
    (pow_nonneg q_sub_one_pos.le _)

theorem numerator_sum :
    rawNormNumerator + oneZeroNormNumerator + oneZeroNormNumerator + normBase =
      (4 * s + 6) * normBase := by
  unfold rawNormNumerator oneZeroNormNumerator
  ring

/-- One input denominator q-1 and one two-output denominator q-1. -/
theorem normalized_four_coefficient_eq :
    ((rawNormNumerator / (q - 1) + oneZeroNormNumerator / (q - 1) +
        oneZeroNormNumerator / (q - 1) + normBase / (q - 1)) / (q - 1)) ^ 2 = C := by
  have hh : rawNormNumerator / (q - 1) + oneZeroNormNumerator / (q - 1) +
      oneZeroNormNumerator / (q - 1) + normBase / (q - 1) =
      (rawNormNumerator + oneZeroNormNumerator + oneZeroNormNumerator + normBase) /
        (q - 1) := by ring
  rw [hh, numerator_sum, div_div, div_pow, mul_pow, normBase_sq]
  have hd : ((q - 1) * (q - 1)) ^ 2 = (q - 1) ^ 4 := by ring
  rw [hd]
  unfold C
  ring

theorem certificate_10_6_entry :
    L (10 : Fin 14) (6 : Fin 14) =
      (1158528657743759 : ℝ) / 3852844238281250000000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 10 6 := by
  rw [certificate_10_6_entry]
  norm_num [AESRound.Terminal.lambda]

-- Factor72 is justified in StepCaps;
-- this scalar comparison alone has no selected-minor or physical conclusion.
theorem certificate_strict_bound : 72 * C < (lambda * L 10 6) ^ 2 := by
  rw [certificate_10_6_entry]
  norm_num [C, rho, kappa, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 10 6 ∧ 72 * C ≤ (lambda * L 10 6) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.TwoOmittedOutputScalar
