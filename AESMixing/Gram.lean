import AESMixing.Product

/-! Gram matrices written as explicit real finite sums, with counting measure. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι α η : Type*} [Fintype α] [Fintype η] [DecidableEq η]

def gram (A : α → ι → ℝ) (i j : ι) : ℝ := ∑ a, A a i * A a j

theorem gram_symmetric (A : α → ι → ℝ) (i j : ι) : gram A i j = gram A j i := by
  simp only [gram, mul_comm]

theorem gram_diagonal (A : α → ι → ℝ) (i : ι) :
    gram A i i = ∑ a, A a i ^ 2 := by simp only [gram, pow_two]

theorem gram_diagonal_nonneg (A : α → ι → ℝ) (i : ι) : 0 ≤ gram A i i := by
  rw [gram_diagonal]
  exact Finset.sum_nonneg (fun a _ => sq_nonneg (A a i))

theorem gram_cauchy (A : α → ι → ℝ) (i j : ι) :
    gram A i j ^ 2 ≤ gram A i i * gram A j j := by
  simpa only [gram, ← pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => A a i) (fun a => A a j)

theorem gram_entry_bound (A : α → ι → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (h : ∀ i, gram A i i ≤ delta) (i j : ι) : |gram A i j| ≤ delta := by
  apply (sq_le_sq₀ (abs_nonneg _) hd).mp
  rw [sq_abs]
  calc
    gram A i j ^ 2 ≤ gram A i i * gram A j j := gram_cauchy A i j
    _ ≤ delta * delta := mul_le_mul (h i) (h j) (gram_diagonal_nonneg A j) hd
    _ = delta ^ 2 := by ring

variable [Fintype ι]

theorem gram_quadratic (A : α → ι → ℝ) (mu : ι → ℝ) :
    (∑ a, (∑ i, A a i * mu i) ^ 2) =
      ∑ i, ∑ j, mu i * mu j * gram A i j := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  simp_rw [gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype ι] in
theorem product_gram (A : η → α → ι → ℝ) (i j : η → ι) :
    gram (fun (a : η → α) (x : η → ι) => ∏ t, A t (a t) (x t)) i j =
      ∏ t, gram (A t) (i t) (j t) := by
  unfold gram
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t a => A t a (i t) * A t a (j t))).symm

/-- The second Gram moment is bounded by a squared adjoint norm times trace. -/
theorem gram_moment_from_adjoint (A : α → ι → ℝ) (nu h : ℝ)
    (hAdj : ∀ x : α → ℝ,
      (∑ i, (∑ a, A a i * x a) ^ 2) ≤ nu ^ 2 * ∑ a, x a ^ 2)
    (hTrace : (∑ j, gram A j j) ≤ h) :
    (∑ j, ∑ i, gram A i j ^ 2) ≤ nu ^ 2 * h := by
  calc
    (∑ j, ∑ i, gram A i j ^ 2) ≤ ∑ j, nu ^ 2 * ∑ a, A a j ^ 2 :=
      Finset.sum_le_sum (fun j _ => hAdj (fun a => A a j))
    _ = nu ^ 2 * ∑ j, gram A j j := by
      simp_rw [gram_diagonal, Finset.mul_sum]
    _ ≤ nu ^ 2 * h := mul_le_mul_of_nonneg_left hTrace (sq_nonneg nu)

end AESMixing
