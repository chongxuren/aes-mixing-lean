import AESMixing.Block

/-! Row/column mass bound for rectangular incidence kernels. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem nonnegative_row_cauchy {I : Type*} [Fintype I]
    (a f : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * f i)^2 ≤ (∑ i, a i) * ∑ i, a i * f i^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i) * f i)
  have hterm (i : I) : Real.sqrt (a i) * (Real.sqrt (a i) * f i) = a i * f i := by
    rw [← mul_assoc, Real.mul_self_sqrt (ha i)]
  simp_rw [hterm, mul_pow, Real.sq_sqrt (ha _)] at h
  exact h

theorem rectangular_schur_energy {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ℝ) (r c : ℝ) (hr : 0 ≤ r)
    (hA : ∀ y x, 0 ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c) (f : I → ℝ) :
    (∑ y, action A f y^2) ≤ (r*c) * ∑ x, f x^2 := by
  have hpoint (y : J) : action A f y^2 ≤ r * ∑ x, A y x * f x^2 :=
    (nonnegative_row_cauchy (A y) f (hA y)).trans
      (mul_le_mul_of_nonneg_right (hrow y)
        (Finset.sum_nonneg (fun x _ => mul_nonneg (hA y x) (sq_nonneg _))))
  calc
    _ ≤ ∑ y, r * ∑ x, A y x * f x^2 := Finset.sum_le_sum (fun y _ => hpoint y)
    _ = r * ∑ x, (∑ y, A y x) * f x^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
    _ ≤ r * ∑ x, c * f x^2 := by
      apply mul_le_mul_of_nonneg_left _ hr
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hcol x) (sq_nonneg _)
    _ = (r*c) * ∑ x, f x^2 := by rw [← Finset.mul_sum, mul_assoc]

end AESMixing
