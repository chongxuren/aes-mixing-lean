import AESMixing.ActivitySpan

/-! Coordinate activity projections preserve the whole-word zero value and
total mass. This identifies the invariant correction of their Gram matrix. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem activityMatrix_pointed (z : V) (hn : 1 < Fintype.card V) :
    PointedBistochastic (activityMatrix z) z := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (Fintype.card V - 1 : ℝ) ≠ 0 := by linarith
  have hr (y : V) : (∑ x, activityMatrix z y x) = 1 := by
    have h := congrFun (activityMatrix_action z (fun _ => 1)) y
    simpa [action, wordAverage, nonzeroMean, hd] using h
  refine ⟨?_, ?_, ?_, ?_, hr⟩
  · intro y x
    unfold activityMatrix
    split_ifs <;> positivity
  · intro x
    simp [activityMatrix]
  · intro y
    by_cases hy : y = z <;> simp [activityMatrix, hy]
  · intro x
    simp_rw [activityMatrix_symmetric z _ x]
    exact hr x

theorem coordinateKernel_pointed (D : I → V → V → ℝ) (z : I → V)
    (h : ∀ i, PointedBistochastic (D i) (z i)) :
    PointedBistochastic (coordinateKernel D) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y x
    exact Finset.prod_nonneg (fun i _ => (h i).nonnegative (y i) (x i))
  · intro x
    simp only [coordinateKernel, (h _).zero_row]
    rw [product_indicator]
    simp only [← funext_iff]
  · intro y
    simp only [coordinateKernel, (h _).zero_column]
    rw [product_indicator]
    simp only [← funext_iff]
  · intro x
    change (∑ y : I → V, ∏ i, D i (y i) (x i)) = 1
    rw [← Fintype.prod_sum (fun i v => D i v (x i))]
    simp only [(h _).column_sum, Finset.prod_const_one]
  · intro y
    change (∑ x : I → V, ∏ i, D i (y i) (x i)) = 1
    rw [← Fintype.prod_sum (fun i v => D i (y i) v)]
    simp only [(h _).row_sum, Finset.prod_const_one]

omit [Fintype I] [DecidableEq I] in
theorem degree_zero_pointed (z : V) (hn : 1 < Fintype.card V) :
    PointedBistochastic (degreeKernel z 0) (fun _ : Fin 4 => z) := by
  rw [degreeKernel_zero]
  change PointedBistochastic (coordinateKernel (fun _ : Fin 4 => activityMatrix z)) _
  exact coordinateKernel_pointed _ _ (fun _ => activityMatrix_pointed z hn)

end AESMixing
