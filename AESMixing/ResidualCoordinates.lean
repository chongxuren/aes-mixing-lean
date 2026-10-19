import AESMixing.PointedProducts

/-! Residual projection on a selected coordinate set. Its outputs vanish
when a marked coordinate is zero, have zero total sum when at least one
coordinate is marked, and do not increase counting-measure energy. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

omit [Fintype I] [DecidableEq I] in
theorem residualProjection_zero_row (z x : V) : residualProjection z z x = 0 := by
  by_cases hx : x = z
  · subst x
    simp [residualProjection, identityKernel, activityMatrix]
  · simp [residualProjection, identityKernel, activityMatrix, hx, Ne.symm hx]

omit [Fintype I] [DecidableEq I] in
theorem degreePiece_column_sum (z : V) (hn : 1 < Fintype.card V)
    (b : Bool) (x : V) : (∑ y, degreePiece z b y x) = if b then 0 else 1 := by
  cases b
  · exact (activityMatrix_pointed z hn).column_sum x
  · change (∑ y, (identityKernel y x - activityMatrix z y x)) = 0
    rw [Finset.sum_sub_distrib, (activityMatrix_pointed z hn).column_sum]
    simp [identityKernel]

theorem productProjection_marked_zero (z : V) (a : I → Bool)
    (k : I) (hk : a k = true) (f : (I → V) → ℝ)
    (y : I → V) (hy : y k = z) : action (productProjection z a) f y = 0 := by
  unfold action
  apply Finset.sum_eq_zero
  intro x _
  have hp : productProjection z a y x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [degreePiece, hk, if_true, hy, residualProjection_zero_row]
  rw [hp, zero_mul]

theorem productProjection_marked_sum (z : V) (hn : 1 < Fintype.card V)
    (a : I → Bool) (k : I) (hk : a k = true) (f : (I → V) → ℝ) :
    (∑ y, action (productProjection z a) f y) = 0 := by
  unfold action
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.sum_mul]
  have hp : (∑ y : I → V, productProjection z a y x) = 0 := by
    unfold productProjection
    rw [← Fintype.prod_sum (fun i v => degreePiece z (a i) v (x i))]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [degreePiece_column_sum z hn, hk, ite_true]
  rw [hp, zero_mul]

theorem productProjection_energy_le (z : V) (hn : 1 < Fintype.card V)
    (a : I → Bool) (f : (I → V) → ℝ) :
    (∑ x, action (productProjection z a) f x^2) ≤ ∑ x, f x^2 := by
  rw [productProjection_pythagoras z hn f]
  exact Finset.single_le_sum (fun b _ => Finset.sum_nonneg
    (fun x _ => sq_nonneg (action (productProjection z b) f x))) (Finset.mem_univ a)

theorem productProjection_inner (z : V) (a : I → Bool) (f g : (I → V) → ℝ) :
    (∑ x, action (productProjection z a) f x * g x) =
      ∑ x, f x * action (productProjection z a) g x := by
  simp only [action, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [productProjection_symmetric z a y x]
  ring

end AESMixing
