import AESMixing.Finite

/-!
A direct real-matrix proof of the weighted common-source estimate.
It expands product columns explicitly, without assuming a Schur-product lemma.
-/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

theorem common_source_energy (A : α → ι → ℝ) (B : β → ι → ℝ)
    (mu : ι → ℝ) (nu : ℝ)
    (hA : ∀ x : ι → ℝ,
      (∑ a, (∑ i, A a i * x i) ^ 2) ≤ nu ^ 2 * ∑ i, x i ^ 2) :
    (∑ b, ∑ a, (∑ i, A a i * (mu i * B b i)) ^ 2) ≤
      nu ^ 2 * ∑ i, mu i ^ 2 * ∑ b, B b i ^ 2 := by
  calc
    (∑ b, ∑ a, (∑ i, A a i * (mu i * B b i)) ^ 2)
        ≤ ∑ b, nu ^ 2 * ∑ i, (mu i * B b i) ^ 2 :=
          Finset.sum_le_sum (fun b _ => hA (fun i => mu i * B b i))
    _ = nu ^ 2 * ∑ i, mu i ^ 2 * ∑ b, B b i ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [mul_pow, Finset.mul_sum]

theorem capped_common_source_two (A : α → ι → ℝ) (B : β → ι → ℝ)
    (mu : ι → ℝ) (nu p h : ℝ) (hp : 0 ≤ p)
    (hA : ∀ x : ι → ℝ,
      (∑ a, (∑ i, A a i * x i) ^ 2) ≤ nu ^ 2 * ∑ i, x i ^ 2)
    (hmu : ∀ i, |mu i| ≤ p)
    (htrace : (∑ i, ∑ b, B b i ^ 2) ≤ h) :
    (∑ b, ∑ a, (∑ i, A a i * (mu i * B b i)) ^ 2) ≤
      nu ^ 2 * p ^ 2 * h := by
  have hm (i : ι) : mu i ^ 2 ≤ p ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (mu i)) hp).mpr (hmu i)
  calc
    (∑ b, ∑ a, (∑ i, A a i * (mu i * B b i)) ^ 2)
        ≤ nu ^ 2 * ∑ i, mu i ^ 2 * ∑ b, B b i ^ 2 := common_source_energy A B mu nu hA
    _ ≤ nu ^ 2 * ∑ i, p ^ 2 * ∑ b, B b i ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg nu)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hm i)
        (Finset.sum_nonneg (fun b _ => sq_nonneg (B b i)))
    _ = nu ^ 2 * p ^ 2 * ∑ i, ∑ b, B b i ^ 2 := by
      rw [← Finset.mul_sum, mul_assoc]
    _ ≤ nu ^ 2 * p ^ 2 * h :=
      mul_le_mul_of_nonneg_left htrace (mul_nonneg (sq_nonneg nu) (sq_nonneg p))

end AESMixing
