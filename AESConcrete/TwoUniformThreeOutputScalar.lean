import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Scalar envelope for two input uniforms and three retained outputs

Lemmas for (11,10). The full, two singleton and intersection responses use
safe norm caps (65536*b,b,b,b), with b^2=rho^4*kappa. The intersection
domination follows from kappa <= rho^2. These scalar inequalities impose no
condition on the arbitrary signed joint amplitude. The response module must
add the four norms before squaring and supply the two original normalizing
weights. Physical factor24 is proved separately.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
namespace AESConcrete.TwoUniformThreeOutputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def baseSquared : ℝ := rho ^ 4 * kappa
def fullNorm (b : ℝ) : ℝ := 65536 * b
def eventNorm (b : ℝ) : ℝ := b

theorem baseSquared_nonneg : 0 ≤ baseSquared :=
  mul_nonneg (pow_nonneg rho_nonneg 4) kappa_nonneg

theorem fullNorm_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ fullNorm b :=
  mul_nonneg (by norm_num) hb

theorem eventNorm_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ eventNorm b := hb

theorem fullNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    fullNorm b ^ 2 = q * rho ^ 4 * kappa := by
  rw [fullNorm, mul_pow, hb]
  norm_num [baseSquared, q] <;> ring

theorem eventNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    eventNorm b ^ 2 = rho ^ 4 * kappa := hb

theorem kappa_le_rho_sq : kappa ≤ rho ^ 2 := by
  norm_num [rho, kappa]

theorem intersection_energy_le_baseSquared : rho ^ 2 * kappa ^ 2 ≤ baseSquared := by
  calc
    _ = (rho ^ 2 * kappa) * kappa := by ring
    _ ≤ (rho ^ 2 * kappa) * rho ^ 2 :=
      mul_le_mul_of_nonneg_left kappa_le_rho_sq
        (mul_nonneg (sq_nonneg rho) kappa_nonneg)
    _ = baseSquared := by unfold baseSquared; ring

theorem intersection_energy_le_eventNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    rho ^ 2 * kappa ^ 2 ≤ eventNorm b ^ 2 := by
  rw [eventNorm, hb]
  exact intersection_energy_le_baseSquared

/-- Selected-piece energy coefficient; no support multiplicity is hidden here. -/
def C : ℝ := baseSquared * (65539 : ℝ) ^ 2 / (q - 1) ^ 2

theorem C_nonneg : 0 ≤ C :=
  div_nonneg (mul_nonneg baseSquared_nonneg (sq_nonneg _)) (sq_nonneg _)

theorem four_coefficient_eq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    (fullNorm b + eventNorm b + eventNorm b + eventNorm b) ^ 2 /
      (q - 1) ^ 2 = C := by
  unfold fullNorm eventNorm C
  have hs : (65536 * b + b + b + b) ^ 2 = (65539 : ℝ) ^ 2 * b ^ 2 := by ring
  rw [hs, hb]
  ring

theorem certificate_11_10_entry :
    L (11 : Fin 14) (10 : Fin 14) =
      (4602766331533291 : ℝ) / 154113769531250000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 11 10 := by
  rw [certificate_11_10_entry]
  norm_num [AESRound.Terminal.lambda]

-- Only the unchanged exact rational certificate is used here. The physical
-- module must establish 6 input supports times 4 orthogonal output energies.
theorem certificate_strict_bound : 24 * C < (lambda * L 11 10) ^ 2 := by
  rw [certificate_11_10_entry]
  norm_num [C, baseSquared, rho, kappa, q, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 11 10 ∧ 24 * C ≤ (lambda * L 11 10) ^ 2 :=
  ⟨le_of_lt certificate_product_pos, le_of_lt certificate_strict_bound⟩

end AESConcrete.TwoUniformThreeOutputScalar
