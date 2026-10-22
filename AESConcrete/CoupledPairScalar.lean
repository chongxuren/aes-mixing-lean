import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Scalar envelope for the joint-residual-pair response

The four coefficients correspond to the full response, each of three single
events, each of three double events, and the surviving triple intersection.
This module only proves scalar implications: it supplies no physical event
energy, fiber identity, factor24 aggregation or operator cap.

The eight norms must be combined before squaring. Fixed constructive
AES10/14/16 scope: independent uniform retained keys, whitening, omitted final
MixColumns, ordered-distinct reference law.
-/

noncomputable section
namespace AESConcrete.CoupledPairScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def fullNorm : ℝ := q * s * rho * kappa
def singleNorm : ℝ := 29 * s * rho * kappa
def doubleNorm : ℝ := 29 * rho * kappa
def tripleNorm : ℝ := rho * kappa

theorem fullNorm_nonneg : 0 ≤ fullNorm := by
  unfold fullNorm
  exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt q_pos) (le_of_lt s_pos))
    rho_nonneg) kappa_nonneg

theorem singleNorm_nonneg : 0 ≤ singleNorm := by
  unfold singleNorm
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos))
    rho_nonneg) kappa_nonneg

theorem doubleNorm_nonneg : 0 ≤ doubleNorm := by
  unfold doubleNorm
  exact mul_nonneg (mul_nonneg (by norm_num) rho_nonneg) kappa_nonneg

theorem tripleNorm_nonneg : 0 ≤ tripleNorm := mul_nonneg rho_nonneg kappa_nonneg

/-- The retained-fiber full response pays q cubed in squared energy. -/
theorem fullNorm_sq : fullNorm ^ 2 = q ^ 3 * rho ^ 2 * kappa ^ 2 := by
  simp only [fullNorm, mul_pow, s_sq]
  ring

theorem tripleNorm_sq : tripleNorm ^ 2 = rho ^ 2 * kappa ^ 2 := by
  unfold tripleNorm
  ring

/-- Exact rational envelope for the intermediate event categories. -/
theorem rho_sq_le_29_sq_mul_kappa : rho ^ 2 ≤ (29 : ℝ) ^ 2 * kappa := by
  norm_num [rho, kappa]

theorem single_energy_le_singleNorm_sq : q * rho ^ 4 * kappa ≤ singleNorm ^ 2 := by
  calc
    _ = (q * rho ^ 2 * kappa) * rho ^ 2 := by ring
    _ ≤ (q * rho ^ 2 * kappa) * ((29 : ℝ) ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (mul_nonneg (mul_nonneg (le_of_lt q_pos) (sq_nonneg rho)) kappa_nonneg)
    _ = _ := by
      simp only [singleNorm, mul_pow, s_sq]
      ring

theorem double_energy_le_doubleNorm_sq : rho ^ 4 * kappa ≤ doubleNorm ^ 2 := by
  calc
    _ = (rho ^ 2 * kappa) * rho ^ 2 := by ring
    _ ≤ (rho ^ 2 * kappa) * ((29 : ℝ) ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (mul_nonneg (sq_nonneg rho) kappa_nonneg)
    _ = _ := by unfold doubleNorm; ring

def C_safe : ℝ :=
  rho ^ 2 * kappa ^ 2 * (q * s + 87 * s + 88) ^ 2 / (q - 1) ^ 3

theorem C_safe_nonneg : 0 ≤ C_safe := by
  unfold C_safe
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)) (sq_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) 3)

/-- The full, three single, three double and triple norms all survive. -/
theorem eight_coefficient_eq :
    (fullNorm + 3 * singleNorm + 3 * doubleNorm + tripleNorm) ^ 2 / (q - 1) ^ 3 =
      C_safe := by
  unfold fullNorm singleNorm doubleNorm tripleNorm C_safe
  ring

/-- Exact unchanged certificate datum, independently of the scalar envelope. -/
theorem certificate_12_10_entry :
    L (12 : Fin 14) (10 : Fin 14) =
      (262855565954471 : ℝ) / 3852844238281250 := rfl

/-- Scalar comparison only. The physical factor24 needs a separate proof. -/
theorem certificate_bound :
    0 ≤ lambda * L 12 10 ∧ 24 * C_safe ≤ (lambda * L 12 10) ^ 2 := by
  rw [certificate_12_10_entry]
  norm_num [C_safe, rho, kappa, q, s, AESRound.Terminal.lambda]

end AESConcrete.CoupledPairScalar
