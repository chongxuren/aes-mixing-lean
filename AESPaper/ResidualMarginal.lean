import AESPaper.LocalAES
import AESPaper.StartingWord
import AESConcrete.RestrictedMarginalEnergy

/-!
# A residual response to a full-uniform centered marginal
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.ResidualMarginal
open AESMixing AESConcrete
open AESPaper.StartingWord (q)

def R : AES.Word → AES.Word → ℝ := residualMatrix AES.wordSuperboxKernel 0

/-- Converse of the existing energy-to-operator wrapper, on the same norm. -/
theorem energy_of_operator_norm {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c) (hD : ‖kernelOperator D‖ ≤ c)
    (f : V → ℝ) :
    (∑ y, action D f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2 := by
  let v : EuclideanSpace ℝ V := WithLp.toLp 2 f
  have hn : ‖kernelOperator D v‖ ≤ c * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm (kernelOperator D) v).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  have hs := (sq_le_sq₀ (norm_nonneg (kernelOperator D v))
    (mul_nonneg hc (norm_nonneg v))).mpr hn
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply, v]
    using hs

/-- Constant densities are fixed by both pointed bistochastic terms. -/
theorem residual_constant (c : ℝ) : action R (fun _ => c) = 0 := by
  have hrow (y : AES.Word) : (∑ x, R y x) = 0 := by
    simp only [R, residualMatrix, Finset.sum_sub_distrib]
    rw [AES.word_superbox_pointed.row_sum,
      (activityMatrix_pointed (0 : AES.Word) AES.word_card_gt_one).row_sum]
    ring
  funext y
  simp only [action, ← Finset.sum_mul, hrow, zero_mul, Pi.zero_apply]

theorem residual_center (f : AES.Word → ℝ) :
    action R (fun x => f x - 1/q) = action R f := by
  change action R (f - (fun _ => 1/q)) = _
  rw [action_sub, residual_constant, sub_zero]

/-- The sharp local resource gives the exact convenient coefficient 441/(4q). -/
theorem residual_energy (f : AES.Word → ℝ) :
    (∑ y, action R f y ^ 2) ≤ (441/(4*q)) * ∑ x, f x ^ 2 := by
  have h := energy_of_operator_norm R (21/131072) (by norm_num)
    (WordFourierVariants.variant_operator_norm_le false false) f
  convert h using 1 <;> norm_num [q]

theorem centered_residual_energy (f : AES.Word → ℝ) :
    (∑ y, action R f y ^ 2) ≤ (441/(4*q)) * ∑ x, (f x-1/q)^2 := by
  have h := residual_energy (fun x => f x-1/q)
  rw [residual_center] at h
  exact h

/-- Two active sources will supply this marginal-energy premise. -/
theorem response_energy_le (f : AES.Word → ℝ)
    (hf : (∑ x, (f x-1/q)^2) ≤ 1/(25*q)) :
    (∑ y, action R f y ^ 2) ≤ 441/(100*q^2) := by
  calc
    _ ≤ (441/(4*q)) * (1/(25*q)) := (centered_residual_energy f).trans
      (mul_le_mul_of_nonneg_left hf (by norm_num [q]))
    _ = _ := by norm_num [q]

end AESPaper.ResidualMarginal
