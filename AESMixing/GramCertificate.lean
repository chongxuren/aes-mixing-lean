import AESMixing.Gram

/-! Soundness of exact weighted-square certificates for Gram domination.
Numerical matrix entries alone are not sufficient: applications must also prove
that they equal the Gram matrices of the concrete response and input columns. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem weighted_square_gram {I K : Type*} [Fintype I] [Fintype K]
    (L : K → I → ℝ) (d : K → ℝ) (x : I → ℝ) :
    (∑ k, d k * (∑ i, L k i * x i)^2) =
      ∑ i, ∑ j, x i * x j * ∑ k, d k * L k i * L k j := by
  have he (k : K) : d k * (∑ i, L k i * x i)^2 =
      ∑ i, ∑ j, x i * x j * (d k * L k i * L k j) := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mul_sum _ _ _).symm

theorem gram_domination_from_certificate {I K A B : Type*}
    [Fintype I] [Fintype K] [Fintype A] [Fintype B]
    (input : A → I → ℝ) (output : B → I → ℝ)
    (L : K → I → ℝ) (d : K → ℝ) (c : ℝ)
    (hd : ∀ k, 0 ≤ d k)
    (hc : ∀ i j, c^2 * gram input i j - gram output i j =
      ∑ k, d k * L k i * L k j) (x : I → ℝ) :
    (∑ b, (∑ i, output b i * x i)^2) ≤ c^2 * ∑ a, (∑ i, input a i * x i)^2 := by
  have he : c^2 * (∑ a, (∑ i, input a i * x i)^2) -
      (∑ b, (∑ i, output b i * x i)^2) = ∑ k, d k * (∑ i, L k i * x i)^2 := by
    rw [gram_quadratic, gram_quadratic, weighted_square_gram]
    simp_rw [← hc]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : 0 ≤ ∑ k, d k * (∑ i, L k i * x i)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hd k) (sq_nonneg _))
  linarith

end AESMixing
