import AESMixing.Product

/-! Squared-operator tensorization on arbitrary joint vectors. No independence
assumption is made about the input vector. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]

def productAction (A : α → ι → ℝ) (B : β → κ → ℝ)
    (x : ι × κ → ℝ) (y : α × β) : ℝ :=
  ∑ i, A y.1 i * ∑ j, B y.2 j * x (i,j)

theorem product_operator_energy (A : α → ι → ℝ) (B : β → κ → ℝ)
    (a b : ℝ)
    (hA : ∀ x : ι → ℝ, (∑ y, (∑ i, A y i * x i) ^ 2) ≤ a ^ 2 * ∑ i, x i ^ 2)
    (hB : ∀ x : κ → ℝ, (∑ y, (∑ j, B y j * x j) ^ 2) ≤ b ^ 2 * ∑ j, x j ^ 2)
    (x : ι × κ → ℝ) :
    (∑ y, productAction A B x y ^ 2) ≤ a ^ 2 * b ^ 2 * ∑ i, x i ^ 2 := by
  simp only [productAction, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    (∑ v, ∑ u, (∑ i, A u i * ∑ j, B v j * x (i,j)) ^ 2) ≤
        ∑ v, a ^ 2 * ∑ i, (∑ j, B v j * x (i,j)) ^ 2 :=
      Finset.sum_le_sum (fun v _ => hA (fun i => ∑ j, B v j * x (i,j)))
    _ = a ^ 2 * ∑ i, ∑ v, (∑ j, B v j * x (i,j)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ a ^ 2 * ∑ i, b ^ 2 * ∑ j, x (i,j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      exact Finset.sum_le_sum (fun i _ => hB (fun j => x (i,j)))
    _ = a ^ 2 * b ^ 2 * ∑ i, ∑ j, x (i,j) ^ 2 := by
      rw [← Finset.mul_sum, mul_assoc]

end AESMixing
