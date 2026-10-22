import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# scalar envelope for the omitted output uniform at (9,7)

The actual output has two retained labels, one zero label and one omitted
nonzero-uniform label. Its response must first be identified as
(W-W0)/sqrt(q-1). The proposed W and W0 norm numerators are (3*s+3)*a and
(s+3)*a, with a=rho*sqrt(kappa), over the same input normalizer. This file
supplies only scalar identities and the certificate margin. The actual output
split, signed original-amplitude bridge, event energies and physical factor48
remain separate proof obligations.

Constructive fixed AES10/14/16; independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
namespace AESConcrete.OmittedUniformTwoOutputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def normBase : ℝ := rho * Real.sqrt kappa
def weightedNormNumerator : ℝ := (3 * s + 3) * normBase
def zeroOutputNormNumerator : ℝ := (s + 3) * normBase
def weightedC : ℝ := weightedNormNumerator ^ 2 / (q - 1) ^ 3
def C : ℝ := rho ^ 2 * kappa * (4 * s + 6) ^ 2 / (q - 1) ^ 4

theorem normBase_nonneg : 0 ≤ normBase :=
  mul_nonneg rho_nonneg (Real.sqrt_nonneg _)

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa := by
  unfold normBase
  rw [mul_pow, Real.sq_sqrt kappa_nonneg]

theorem weightedNormNumerator_nonneg : 0 ≤ weightedNormNumerator :=
  mul_nonneg (add_nonneg (mul_nonneg (by norm_num) s_pos.le) (by norm_num))
    normBase_nonneg

theorem zeroOutputNormNumerator_nonneg : 0 ≤ zeroOutputNormNumerator :=
  mul_nonneg (add_nonneg s_pos.le (by norm_num)) normBase_nonneg

theorem singleNorm_sq : (s * normBase) ^ 2 = q * rho ^ 2 * kappa := by
  rw [mul_pow, s_sq, normBase_sq]
  ring

theorem weighted_coefficient_eq :
    (0 + 3 * (s * normBase) + 3 * normBase) ^ 2 / (q - 1) ^ 3 = weightedC := by
  unfold weightedC weightedNormNumerator
  ring

theorem zeroOutput_coefficient_eq :
    zeroOutputNormNumerator ^ 2 / (q - 1) ^ 3 =
      rho ^ 2 * kappa * (s + 3) ^ 2 / (q - 1) ^ 3 := by
  unfold zeroOutputNormNumerator
  rw [mul_pow, normBase_sq]
  ring

theorem C_nonneg : 0 ≤ C :=
  div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg _))
    (pow_nonneg q_sub_one_pos.le _)

theorem numerator_sum_sq :
    (weightedNormNumerator + zeroOutputNormNumerator) ^ 2 =
      rho ^ 2 * kappa * (4 * s + 6) ^ 2 := by
  have he : weightedNormNumerator + zeroOutputNormNumerator =
      normBase * (4 * s + 6) := by
    unfold weightedNormNumerator zeroOutputNormNumerator
    ring
  rw [he, mul_pow, normBase_sq]

theorem coefficient_eq :
    (weightedNormNumerator + zeroOutputNormNumerator) ^ 2 / (q - 1) ^ 4 = C := by
  rw [numerator_sum_sq]
  rfl

theorem certificate_9_7_entry :
    L (9 : Fin 14) (7 : Fin 14) =
      (945934687954567 : ℝ) / 3852844238281250000000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 9 7 := by
  rw [certificate_9_7_entry]
  norm_num [AESRound.Terminal.lambda]

-- Four input supports times twelve orthogonal output energies is a separate
-- physical aggregation obligation. This comparison alone proves no step cap.
theorem certificate_strict_bound : 48 * C < (lambda * L 9 7) ^ 2 := by
  rw [certificate_9_7_entry]
  norm_num [C, rho, kappa, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 9 7 ∧ 48 * C ≤ (lambda * L 9 7) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.OmittedUniformTwoOutputScalar
