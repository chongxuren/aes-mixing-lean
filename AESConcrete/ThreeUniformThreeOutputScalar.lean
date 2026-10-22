import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Scalar envelope for three original uniforms and three retained outputs

Candidate (11,7). The seven response norms are q*a, three copies of
29*s*a, and three copies of a, where a=rho*kappa. The triple-zero
kernel cancellation and the physical factor16 are separate obligations.
The same arbitrary signed residual-singleton amplitude is retained throughout.
Constructive independent-retained-key AES10/14/16, whitening, omitted final
MixColumns, ordered-distinct reference; no attacks. Compilation and independent
review are required before acceptance. No manuscript changes.
-/

noncomputable section
namespace AESConcrete.ThreeUniformThreeOutputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def normBase : ℝ := rho * kappa
def fullNorm : ℝ := q * normBase
def singleNorm : ℝ := 29 * s * normBase
def doubleNorm : ℝ := normBase

theorem normBase_nonneg : 0 ≤ normBase := mul_nonneg rho_nonneg kappa_nonneg
theorem fullNorm_nonneg : 0 ≤ fullNorm :=
  mul_nonneg (le_of_lt q_pos) normBase_nonneg
theorem singleNorm_nonneg : 0 ≤ singleNorm :=
  mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) normBase_nonneg
theorem doubleNorm_nonneg : 0 ≤ doubleNorm := normBase_nonneg

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa ^ 2 := by
  unfold normBase
  ring

theorem fullNorm_sq : fullNorm ^ 2 = q ^ 2 * rho ^ 2 * kappa ^ 2 := by
  unfold fullNorm
  rw [mul_pow, normBase_sq]
  ring

theorem doubleNorm_sq : doubleNorm ^ 2 = rho ^ 2 * kappa ^ 2 := normBase_sq

theorem rho_sq_le_29_sq_mul_kappa : rho ^ 2 ≤ 29 ^ 2 * kappa := by
  norm_num [rho, kappa]

theorem single_energy_le_singleNorm_sq : q * rho ^ 4 * kappa ≤ singleNorm ^ 2 := by
  calc
    _ = (q * rho ^ 2 * kappa) * rho ^ 2 := by ring
    _ ≤ (q * rho ^ 2 * kappa) * (29 ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (mul_nonneg (mul_nonneg (le_of_lt q_pos) (sq_nonneg rho)) kappa_nonneg)
    _ = _ := by rw [← s_sq]; unfold singleNorm normBase; ring

/-- Selected-piece coefficient, with three original normalizing weights. -/
def C : ℝ := rho ^ 2 * kappa ^ 2 * (q + 87 * s + 3) ^ 2 / (q - 1) ^ 3

theorem C_nonneg : 0 ≤ C :=
  div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)) (sq_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) _)

theorem seven_coefficient_eq :
    (fullNorm + 3 * singleNorm + 3 * doubleNorm) ^ 2 / (q - 1) ^ 3 = C := by
  unfold fullNorm singleNorm doubleNorm normBase C
  ring

theorem certificate_11_7_entry :
    L (11 : Fin 14) (7 : Fin 14) =
      (1311660880739703 : ℝ) / 1541137695312500000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 11 7 := by
  rw [certificate_11_7_entry]
  norm_num [AESRound.Terminal.lambda]

-- Four input supports and four orthogonal output energies must be proved
-- in StepCaps. This exact rational check alone is not an operator bound.
theorem certificate_strict_bound : 16 * C < (lambda * L 11 7) ^ 2 := by
  rw [certificate_11_7_entry]
  norm_num [C, rho, kappa, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 11 7 ∧ 16 * C ≤ (lambda * L 11 7) ^ 2 :=
  ⟨le_of_lt certificate_product_pos, le_of_lt certificate_strict_bound⟩

end AESConcrete.ThreeUniformThreeOutputScalar
