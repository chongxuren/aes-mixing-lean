import AESMixing.Averaging
import AESMixing.ByteResources

/-! Exact commutation with the activity projection. This supplies the
substitution factorization without assuming product input distributions. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

structure PointedBistochastic (D : V → V → ℝ) (z : V) : Prop where
  nonnegative : ∀ b a, 0 ≤ D b a
  zero_row : ∀ a, D z a = if a = z then 1 else 0
  zero_column : ∀ b, D b z = if b = z then 1 else 0
  column_sum : ∀ a, (∑ b, D b a) = 1
  row_sum : ∀ b, (∑ a, D b a) = 1

theorem PointedBistochastic.action_sum {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (f : V → ℝ) :
    (∑ y, action D f y) = ∑ x, f x := by
  unfold action
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h.column_sum, one_mul]

theorem PointedBistochastic.action_zero {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (f : V → ℝ) : action D f z = f z := by
  simp only [action, h.zero_row, ite_mul, one_mul, zero_mul]
  simp

theorem PointedBistochastic.average_action {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (f : V → ℝ) :
    wordAverage z (action D f) = wordAverage z f := by
  funext x
  simp only [wordAverage, nonzeroMean, h.action_sum, h.action_zero]

theorem PointedBistochastic.action_average {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (f : V → ℝ) :
    action D (wordAverage z f) = wordAverage z f := by
  have hp (x : V) : wordAverage z f x = nonzeroMean z f +
      if x = z then f z - nonzeroMean z f else 0 := by
    by_cases hx : x = z <;> simp [wordAverage, hx]
  funext y
  unfold action
  simp_rw [hp, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_ite, mul_zero]
  rw [h.row_sum, one_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, h.zero_column]
  by_cases hy : y = z <;> simp [hy]

def activityMatrix (z : V) (y x : V) : ℝ :=
  if y = z then (if x = z then 1 else 0)
  else if x = z then 0 else 1 / (Fintype.card V - 1 : ℝ)

theorem activityMatrix_action (z : V) (f : V → ℝ) :
    action (activityMatrix z) f = wordAverage z f := by
  funext y
  by_cases hy : y = z
  · subst y
    simp [action, activityMatrix, wordAverage]
  · have hp (x : V) : activityMatrix z y x * f x =
        (f x - if x = z then f z else 0) / (Fintype.card V - 1 : ℝ) := by
      by_cases hx : x = z
      · subst x; simp [activityMatrix, hy]
      · simp [activityMatrix, hy, hx, div_eq_mul_inv, mul_comm]
    simp only [action, hp, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp [wordAverage, hy, nonzeroMean]

def residualMatrix (D : V → V → ℝ) (z : V) (y x : V) : ℝ := D y x - activityMatrix z y x

theorem residualMatrix_action {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (f : V → ℝ) :
    action (residualMatrix D z) f = action D (wordResidual z f) := by
  rw [wordResidual, action_sub, h.action_average]
  funext y
  simp only [action, residualMatrix, sub_mul, Finset.sum_sub_distrib, Pi.sub_apply]
  exact congrArg ((∑ x, D y x * f x) - ·) (congrFun (activityMatrix_action z f) y)

theorem residual_energy_le (z : V) (f : V → ℝ) (hn : 1 < Fintype.card V) :
    (∑ x, wordResidual z f x^2) ≤ ∑ x, f x^2 := by
  have he := activity_residual_pythagoras z f hn
  have hp : 0 ≤ ∑ x, wordAverage z f x^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem residualMatrix_energy {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (hn : 1 < Fintype.card V) (s : ℝ)
    (hnorm : ∀ f : V → ℝ, f z = 0 → (∑ x, f x) = 0 →
      (∑ y, action D f y^2) ≤ s^2 * ∑ x, f x^2) (f : V → ℝ) :
    (∑ y, action (residualMatrix D z) f y^2) ≤ s^2 * ∑ x, f x^2 := by
  rw [residualMatrix_action h]
  exact (hnorm _ (wordResidual_at_zero z f) (wordResidual_sum z f hn)).trans
    (mul_le_mul_of_nonneg_left (residual_energy_le z f hn) (sq_nonneg s))

theorem ByteResources.pointed {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) : PointedBistochastic D 0 :=
  ⟨h.nonnegative, h.zero_row, h.zero_column, h.column_sum, h.row_sum⟩

theorem ByteResources.residual_matrix_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (f : BinaryWord 8 → ℝ) :
    (∑ y, action (residualMatrix D 0) f y^2) ≤ (9 / 128 : ℝ)^2 * ∑ x, f x^2 :=
  residualMatrix_energy h.pointed (by norm_num [BinaryWord.card]) (9/128) h.residual f

end AESMixing
