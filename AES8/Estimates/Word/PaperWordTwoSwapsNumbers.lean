import AES8.Estimates.Word.PaperWordDegreeComparison

/-! The paper's uniform HS/operator assignment and exactly two swaps.
All decimals are exact rationals. These are scalar tables; their physical
operator interpretation is supplied in a separate assembly leaf. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperWordTwoSwapsNumbers
open AESConcrete.WordMomentNumbers
open PaperWordDegreeComparison
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def uniform (i j : Fin 5) : ℝ := ∑ k, hs k i * comparison k j

def saving (j : Fin 5) : ℝ := hs 1 1 * comparison 1 j - comparison 1 1 * hs 1 j

def upper (i j : Fin 5) : ℝ :=
  uniform i j - if i = 1 ∧ (j = 2 ∨ j = 3) then saving j else 0

/-- The lower Gram blocks use the adjoints of the upper blocks. -/
def bound (i j : Fin 5) : ℝ := if i ≤ j then upper i j else upper j i

/-- Swap only the distinguished block row in entries (1,2) and (1,3). -/
def chosen (k i j : Fin 5) : ℝ :=
  if k = 1 ∧ i = 1 ∧ (j = 2 ∨ j = 3) then comparison k i * hs k j
  else hs k i * comparison k j

theorem sum_five (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + f 4))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem chosen_sum (i j : Fin 5) : (∑ k, chosen k i j) = upper i j := by
  unfold upper uniform saving chosen
  simp only [sum_five]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] <;> ring

theorem chosen_nonneg (k i j : Fin 5) : 0 ≤ chosen k i j := by
  unfold chosen
  split_ifs
  · exact mul_nonneg (comparison_nonneg _ _) (hs_nonneg _ _)
  · exact mul_nonneg (hs_nonneg _ _) (comparison_nonneg _ _)

theorem upper_nonneg (i j : Fin 5) : 0 ≤ upper i j := by
  rw [← chosen_sum]
  exact Finset.sum_nonneg (fun k _ => chosen_nonneg k i j)

theorem bound_nonneg (i j : Fin 5) : 0 ≤ bound i j := by
  unfold bound
  split_ifs <;> exact upper_nonneg _ _

theorem min_le_chosen (k i j : Fin 5) :
    min (hs k i * comparison k j) (comparison k i * hs k j) ≤ chosen k i j := by
  unfold chosen
  split_ifs
  · exact min_le_right _ _
  · exact min_le_left _ _

theorem min_sum_le_bound (i j : Fin 5) :
    (∑ k, min (hs k i * comparison k j) (comparison k i * hs k j)) ≤ bound i j := by
  unfold bound
  split_ifs with h
  · rw [← chosen_sum]
    exact Finset.sum_le_sum (fun k _ => min_le_chosen k i j)
  · have he : (∑ k, min (hs k i * comparison k j) (comparison k i * hs k j)) =
        ∑ k, min (hs k j * comparison k i) (comparison k j * hs k i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_comm (hs k i), mul_comm (comparison k i), min_comm]
    rw [he, ← chosen_sum]
    exact Finset.sum_le_sum (fun k _ => min_le_chosen k j i)

def rowSquares (i : Fin 5) : ℝ :=
  uniform i i ^ 2 + 2 * ∑ j, if i < j then uniform i j ^ 2 else 0

def rowLimit : Fin 5 → ℝ := ![33163,22966,33565,4482,68]

theorem uniform_rows (i : Fin 5) : rowSquares i < rowLimit i := by
  fin_cases i
  · simp only [rowSquares, sum_five]
    change uniform 0 0 ^ 2 + 2 * (0 + (uniform 0 1 ^ 2 + (uniform 0 2 ^ 2 + (uniform 0 3 ^ 2 + (uniform 0 4 ^ 2))))) < 33163
    norm_num [uniform, sum_five, hs, comparison,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · simp only [rowSquares, sum_five]
    change uniform 1 1 ^ 2 + 2 * (0 + (0 + (uniform 1 2 ^ 2 + (uniform 1 3 ^ 2 + (uniform 1 4 ^ 2))))) < 22966
    norm_num [uniform, sum_five, hs, comparison,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · simp only [rowSquares, sum_five]
    change uniform 2 2 ^ 2 + 2 * (0 + (0 + (0 + (uniform 2 3 ^ 2 + (uniform 2 4 ^ 2))))) < 33565
    norm_num [uniform, sum_five, hs, comparison,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · simp only [rowSquares, sum_five]
    change uniform 3 3 ^ 2 + 2 * (0 + (0 + (0 + (0 + (uniform 3 4 ^ 2))))) < 4482
    norm_num [uniform, sum_five, hs, comparison,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · simp only [rowSquares, sum_five]
    change uniform 4 4 ^ 2 + 2 * (0 + (0 + (0 + (0 + (0))))) < 68
    norm_num [uniform, sum_five, hs, comparison,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem uniform_total_lt : (∑ i, rowSquares i) < 94250 := by
  have h := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5)))
    Finset.univ_nonempty (fun i _ => uniform_rows i)
  have hn : (∑ i : Fin 5, rowLimit i) = 94244 := by norm_num [rowLimit, sum_five, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  rw [hn] at h
  linarith

theorem saving_two : saving 2 = 1192 / 100 := by norm_num [saving, hs, comparison, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
theorem saving_three : saving 3 = 9961 / 1000 := by norm_num [saving, hs, comparison, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
theorem uniform_two : uniform 1 2 = 740618 / 10000 := by
  norm_num [uniform, sum_five, hs, comparison, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
theorem uniform_three : uniform 1 3 = 33821464 / 1000000 := by
  norm_num [uniform, sum_five, hs, comparison, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

def improvement (j : Fin 5) : ℝ := 2 * saving j * (2 * uniform 1 j - saving j)

theorem improvement_two : 3240 < improvement 2 := by
  norm_num [improvement, saving_two, uniform_two]
theorem improvement_three : 1140 < improvement 3 := by
  norm_num [improvement, saving_three, uniform_three]

/-- Exact removal of the two changed terms, each including its adjoint. -/
theorem two_swap_identity : (∑ i, ∑ j, bound i j ^ 2) =
    (∑ i, rowSquares i) - improvement 2 - improvement 3 := by
  simp only [rowSquares, sum_five]
  change ((uniform 0 0 - 0) ^ 2 + ((uniform 0 1 - 0) ^ 2 + ((uniform 0 2 - 0) ^ 2 + ((uniform 0 3 - 0) ^ 2 + ((uniform 0 4 - 0) ^ 2))))) + (((uniform 0 1 - 0) ^ 2 + ((uniform 1 1 - 0) ^ 2 + ((uniform 1 2 - saving 2) ^ 2 + ((uniform 1 3 - saving 3) ^ 2 + ((uniform 1 4 - 0) ^ 2))))) + (((uniform 0 2 - 0) ^ 2 + ((uniform 1 2 - saving 2) ^ 2 + ((uniform 2 2 - 0) ^ 2 + ((uniform 2 3 - 0) ^ 2 + ((uniform 2 4 - 0) ^ 2))))) + (((uniform 0 3 - 0) ^ 2 + ((uniform 1 3 - saving 3) ^ 2 + ((uniform 2 3 - 0) ^ 2 + ((uniform 3 3 - 0) ^ 2 + ((uniform 3 4 - 0) ^ 2))))) + (((uniform 0 4 - 0) ^ 2 + ((uniform 1 4 - 0) ^ 2 + ((uniform 2 4 - 0) ^ 2 + ((uniform 3 4 - 0) ^ 2 + ((uniform 4 4 - 0) ^ 2))))))))) =
    (uniform 0 0 ^ 2 + 2 * (0 + (uniform 0 1 ^ 2 + (uniform 0 2 ^ 2 + (uniform 0 3 ^ 2 + (uniform 0 4 ^ 2)))))) + ((uniform 1 1 ^ 2 + 2 * (0 + (0 + (uniform 1 2 ^ 2 + (uniform 1 3 ^ 2 + (uniform 1 4 ^ 2)))))) + ((uniform 2 2 ^ 2 + 2 * (0 + (0 + (0 + (uniform 2 3 ^ 2 + (uniform 2 4 ^ 2)))))) + ((uniform 3 3 ^ 2 + 2 * (0 + (0 + (0 + (0 + (uniform 3 4 ^ 2)))))) + ((uniform 4 4 ^ 2 + 2 * (0 + (0 + (0 + (0 + (0)))))))))) -
      2 * saving 2 * (2 * uniform 1 2 - saving 2) -
      2 * saving 3 * (2 * uniform 1 3 - saving 3)
  ring

/-- The literal 94250 - 3240 - 1140 argument printed in the paper. -/
theorem two_swap_total_lt : (∑ i, ∑ j, bound i j ^ 2) < 89870 := by
  rw [two_swap_identity]
  linarith [uniform_total_lt, improvement_two, improvement_three]

end AES8.PaperWordTwoSwapsNumbers
