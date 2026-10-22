import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Scalar envelope for the joint-residual-triple response

The four scalar caps correspond to the full response, the two single
exclusions, and their surviving intersection. All four responses must retain
the same arbitrary signed JOINT triple-residual amplitude.

Editorial choice: parameterize the common norm base by its square. This keeps
square-root expressions out of the scalar module. The assembly may take the
nonnegative base `rho^2 * sqrt(kappa)`; this is a scalar choice, not a new
condition on the joint amplitude. Use the existing
`TripleResponse.weightedResponse_energy_le` for four-response aggregation; no
duplicate response theorem or FourResponse module is introduced here.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.

This module gives only scalar identities and comparisons: no source/fiber or
event estimate, normalized minor bridge, physical factor16 proof or operator
cap.
-/

noncomputable section
namespace AESConcrete.CoupledTripleScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

/-- Squared common base for the two-operator, one-column response estimate. -/
def baseSquared : ℝ := rho ^ 4 * kappa

def fullNorm (b : ℝ) : ℝ := q * b
def singleNorm (b : ℝ) : ℝ := 29 * b
def intersectionNorm (b : ℝ) : ℝ := b

theorem baseSquared_nonneg : 0 ≤ baseSquared :=
  mul_nonneg (pow_nonneg rho_nonneg 4) kappa_nonneg

theorem fullNorm_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ fullNorm b :=
  mul_nonneg (le_of_lt q_pos) hb

theorem singleNorm_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ singleNorm b :=
  mul_nonneg (by norm_num) hb

theorem intersectionNorm_nonneg (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ intersectionNorm b := hb

/--
The full-fiber estimate pays q squared, not the pair route's q cubed.
-/
theorem fullNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    fullNorm b ^ 2 = q ^ 2 * rho ^ 4 * kappa := by
  rw [fullNorm, mul_pow, hb]
  unfold baseSquared
  ring

theorem intersectionNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    intersectionNorm b ^ 2 = rho ^ 4 * kappa := hb

/-- Exact rational domination used for each of the two single exclusions. -/
theorem rho_sq_le_29_sq_mul_kappa : rho ^ 2 ≤ (29 : ℝ) ^ 2 * kappa := by
  norm_num [rho, kappa]

theorem single_energy_le_safe : rho ^ 6 ≤ (29 : ℝ) ^ 2 * baseSquared := by
  calc
    _ = rho ^ 4 * rho ^ 2 := by ring
    _ ≤ rho ^ 4 * ((29 : ℝ) ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (pow_nonneg rho_nonneg 4)
    _ = _ := by unfold baseSquared; ring

theorem single_energy_le_singleNorm_sq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    rho ^ 6 ≤ singleNorm b ^ 2 := by
  calc
    _ ≤ (29 : ℝ) ^ 2 * baseSquared := single_energy_le_safe
    _ = singleNorm b ^ 2 := by rw [singleNorm, mul_pow, hb]

/-- Selected-piece coefficient only; physical support multiplicities are separate. -/
def C3 : ℝ := baseSquared * (q + 59) ^ 2 / (q - 1) ^ 2

theorem C3_eq : C3 = rho ^ 4 * kappa * (q + 59) ^ 2 / (q - 1) ^ 2 := rfl

theorem C3_nonneg : 0 ≤ C3 :=
  div_nonneg (mul_nonneg baseSquared_nonneg (sq_nonneg _)) (sq_nonneg _)

-- assembly: use caps (fullNorm b, singleNorm b, singleNorm b,
-- intersectionNorm b) in TripleResponse.weightedResponse_energy_le. Its
-- comparator is the original joint h; the lifted source amplitude is separate.
/-- All four norms are added before squaring, with exactly two unit weights. -/
theorem four_coefficient_eq (b : ℝ) (hb : b ^ 2 = baseSquared) :
    (fullNorm b + singleNorm b + singleNorm b + intersectionNorm b) ^ 2 /
        (q - 1) ^ 2 = C3 := by
  unfold fullNorm singleNorm intersectionNorm C3
  have hs : (q * b + 29 * b + 29 * b + b) ^ 2 = (q + 59) ^ 2 * b ^ 2 := by
    ring
  rw [hs, hb]
  ring

/-- Exact unchanged certificate datum, independent of any physical energy proof. -/
theorem certificate_12_12_entry :
    L (12 : Fin 14) (12 : Fin 14) =
      (492572028294083 : ℝ) / 308227539062500 := rfl

theorem certificate_product_pos : 0 < lambda * L 12 12 := by
  rw [certificate_12_12_entry]
  norm_num [AESRound.Terminal.lambda]

-- The numeral 16 is only a scalar comparison here. A later physical module
-- must derive input multiplicity 4 and the orthogonal sum over 4 output supports.
theorem certificate_strict_bound : 16 * C3 < (lambda * L 12 12) ^ 2 := by
  rw [certificate_12_12_entry]
  norm_num [C3, baseSquared, rho, kappa, q, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 12 12 ∧ 16 * C3 ≤ (lambda * L 12 12) ^ 2 :=
  ⟨le_of_lt certificate_product_pos, le_of_lt certificate_strict_bound⟩

end AESConcrete.CoupledTripleScalar
