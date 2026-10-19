import AESMixing.Gram

/-! A residual norm estimate passes to the transpose of a doubly stochastic
channel fixing zero. The proof is finite Cauchy--Schwarz, not a spectral axiom. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem transpose_residual_energy (A : V → V → ℝ) (zero : V) (c : ℝ)
    (hcolumn0 : ∀ b, A b zero = if b = zero then 1 else 0)
    (hrow : ∀ b, (∑ a, A b a) = 1)
    (hnorm : ∀ f : V → ℝ, f zero = 0 → (∑ a, f a) = 0 →
      (∑ b, (∑ a, A b a * f a)^2) ≤ c * ∑ a, f a^2)
    (x : V → ℝ) (hx0 : x zero = 0) (hx : ∑ b, x b = 0) :
    (∑ a, (∑ b, A b a * x b)^2) ≤ c * ∑ b, x b^2 := by
  let y : V → ℝ := fun a => ∑ b, A b a * x b
  have hy0 : y zero = 0 := by
    simp only [y, hcolumn0, ite_mul, one_mul, zero_mul]
    simpa using hx0
  have hys : (∑ a, y a) = 0 := by
    dsimp only [y]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hrow, one_mul]
    exact hx
  have he : (∑ a, y a^2) = ∑ b, x b * (∑ a, A b a * y a) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hp (a : V) : y a^2 = ∑ b, x b * (A b a * y a) := by
      calc
        y a^2 = (∑ b, A b a * x b) * y a := by change y a^2 = y a * y a; ring
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro b _
          ring
    exact Finset.sum_congr rfl (fun a _ => hp a)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x
    (fun b => ∑ a, A b a * y a)
  rw [← he] at hc
  have hnormy := hnorm y hy0 hys
  have hxnonneg : 0 ≤ ∑ b, x b^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hynonneg : 0 ≤ ∑ a, y a^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hnormy hxnonneg
  change (∑ a, y a^2) ≤ c * ∑ b, x b^2
  by_cases hzero : (∑ a, y a^2) = 0
  · rw [hzero]
    exact (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans (hnorm x hx0 hx)
  · have hpos : 0 < ∑ a, y a^2 := lt_of_le_of_ne hynonneg (Ne.symm hzero)
    nlinarith [hc, hnormy]

end AESMixing
