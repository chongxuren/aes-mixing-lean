import AESMixing.Gram
import Mathlib.Algebra.BigOperators.Field

/-! An alternative real-matrix route to the byte inversion estimate.
Its concrete finite identities are separate obligations, not assumed AES facts. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sign_gram_energy (H : ι → ι → ℝ)
    (hH : ∀ i j, gram H i j = (if i = j then 256 else 0) - 1)
    (x : ι → ℝ) :
    (∑ y, (∑ i, H y i * x i) ^ 2) =
      256 * (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 := by
  rw [gram_quadratic]
  simp_rw [hH, mul_sub, mul_one, Finset.sum_sub_distrib]
  have hdiag : (∑ i, ∑ j, x i * x j * (if i = j then (256 : ℝ) else 0)) =
      256 * ∑ i, x i ^ 2 := by
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag, ← Finset.sum_mul_sum, pow_two]

omit [DecidableEq ι] in
theorem sum_two_energy (a b : ι → ℝ) :
    (∑ i, (a i + 2 * b i) ^ 2) ≤
      (9 / 8 : ℝ) * (∑ i, a i ^ 2) + 36 * ∑ i, b i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (a i - 16 * b i)]

/-- On the zero-sum space, J contributes zero, H contributes norm 16,
and twice a permutation contributes norm 2. This gives (16+2)/256. -/
theorem byte_residual_from_sign_gram (D H : ι → ι → ℝ) (e : Equiv.Perm ι)
    (hH : ∀ i j, gram H i j = (if i = j then 256 else 0) - 1)
    (hD : ∀ y i, D y i =
      (1 + H y i + 2 * (if e y = i then (1 : ℝ) else 0)) / 256)
    (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    (∑ y, (∑ i, D y i * x i) ^ 2) ≤ (9 / 128 : ℝ) ^ 2 * ∑ i, x i ^ 2 := by
  have hact (y : ι) : (∑ i, D y i * x i) =
      ((∑ i, H y i * x i) + 2 * x (e y)) / 256 := by
    have hp (i : ι) : D y i * x i =
        (x i + H y i * x i + 2 * (if e y = i then x i else 0)) / 256 := by
      rw [hD]
      split_ifs <;> ring
    simp_rw [hp]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx]
    simp
  have hsign := sign_gram_energy H hH x
  rw [hx, zero_pow (by decide), sub_zero] at hsign
  have hperm : (∑ y, x (e y) ^ 2) = ∑ i, x i ^ 2 :=
    Equiv.sum_comp e (fun i => x i ^ 2)
  have hsum := sum_two_energy (fun y => ∑ i, H y i * x i) (fun y => x (e y))
  rw [hsign, hperm] at hsum
  simp_rw [hact, div_pow]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256 ^ 2)).mpr
  nlinarith

end AESMixing
