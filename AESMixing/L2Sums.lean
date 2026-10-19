import AESMixing.Block

/-! Triangle and scaling rules for finite real Euclidean vectors, stated
in the same counting-measure norm as the incidence estimates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {I J : Type*} [Fintype I]

theorem l2_zero : l2 (fun _ : I => (0 : ℝ)) = 0 := by simp [l2]

theorem abs_inner_le_l2 (f g : I → ℝ) :
    |∑ x, f x * g x| ≤ l2 f * l2 g := by
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (l2_nonneg _) (l2_nonneg _))).mp
  rw [sq_abs, mul_pow, l2_sq, l2_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

theorem l2_scale (c : ℝ) (f : I → ℝ) :
    l2 (fun x => c * f x) = |c| * l2 f := by
  apply (sq_eq_sq₀ (l2_nonneg _) (mul_nonneg (abs_nonneg _) (l2_nonneg _))).mp
  simp only [l2_sq, mul_pow, ← Finset.mul_sum, sq_abs]

theorem l2_le_of_energy (f : I → ℝ) {J : Type*} [Fintype J]
    (g : J → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : (∑ x, f x^2) ≤ c^2 * ∑ y, g y^2) : l2 f ≤ c*l2 g := by
  apply (sq_le_sq₀ (l2_nonneg _) (mul_nonneg hc (l2_nonneg _))).mp
  simpa only [mul_pow, l2_sq] using h

theorem l2_finset_sum_le [DecidableEq J] (s : Finset J) (f : J → I → ℝ) :
    l2 (fun x => ∑ j ∈ s, f j x) ≤ ∑ j ∈ s, l2 (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [l2]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (l2_add_le (f j) (fun x => ∑ a ∈ s, f a x)).trans
      (add_le_add le_rfl ih)

end AESMixing
