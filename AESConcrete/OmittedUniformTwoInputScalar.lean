import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Proposed scalar comparison for the omitted-output (9,6) route

The source has one inactive input, one residual input and two input uniforms.
The proposed actual output split is (W-W0)/sqrt(q-1). The separate response
obligations propose W numerator (s+2)*a and W0 numerator a over q-1, where
a=rho*sqrt(kappa). Physical factor144 must be proved from twelve input
supports and twelve orthogonal output energies. This scalar file assumes none
of those analytic conclusions and proves no physical step cap by itself.

Constructive fixed AES10/14/16; independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.
-/

noncomputable section
namespace AESConcrete.OmittedUniformTwoInputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s s_pos q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def normBase : ℝ := rho * Real.sqrt kappa

def C : ℝ := rho ^ 2 * kappa * (s + 3) ^ 2 / (q - 1) ^ 3

theorem normBase_nonneg : 0 ≤ normBase :=
  mul_nonneg rho_nonneg (Real.sqrt_nonneg _)

theorem normBase_sq : normBase ^ 2 = rho ^ 2 * kappa := by
  unfold normBase
  rw [mul_pow, Real.sq_sqrt kappa_nonneg]

theorem coefficient_eq :
    (((s + 2) * normBase + normBase) ^ 2 / (q - 1) ^ 3) = C := by
  have hn : (s + 2) * normBase + normBase = normBase * (s + 3) := by ring
  rw [hn, mul_pow, normBase_sq]
  rfl

theorem C_nonneg : 0 ≤ C :=
  div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg _))
    (pow_nonneg q_sub_one_pos.le _)

theorem certificate_9_6_entry :
    L (9 : Fin 14) (6 : Fin 14) =
      (1073770947732399 : ℝ) / 154113769531250000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 9 6 := by
  rw [certificate_9_6_entry]
  norm_num [AESRound.Terminal.lambda]

-- The scalar comparison and analytic factor144 require their own proofs;
-- neither follows merely from this module's existence.
theorem certificate_strict_bound : 144 * C < (lambda * L 9 6) ^ 2 := by
  rw [certificate_9_6_entry]
  norm_num [C, rho, kappa, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 9 6 ∧ 144 * C ≤ (lambda * L 9 6) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.OmittedUniformTwoInputScalar
