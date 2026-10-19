import AESConcrete.WordMomentNumbers

/-!
# Exact source and second-response tables for the fixed 14.3 + 73.1k target
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators Matrix

namespace AESPaper.SourceNumbers
open AESConcrete.WordMomentNumbers (op)

def sourceZ (t : ℕ) : Fin 5 → ℝ :=
  match t with
  | 1 => ![126/1000,144/1000,231/1000,187/1000,95/1000]
  | 2 => ![133/1000,220/1000,92/1000,56/1000,11/1000]
  | 3 => ![149/1000,221/1000,31/1000,6/1000,2/1000]
  | 4 => ![137/1000,221/1000,27/1000,3/1000,1/1000]
  | _ => 0

def responseY (t : ℕ) : Fin 5 → ℝ :=
  match t with
  | 1 => ![2627/1000,941/1000,1225/1000,676/1000,222/1000]
  | 2 => ![1464/1000,531/1000,1192/1000,804/1000,240/1000]
  | 3 => ![1105/1000,329/1000,1174/1000,852/1000,266/1000]
  | 4 => ![999/1000,316/1000,1112/1000,811/1000,246/1000]
  | _ => 0

theorem sum_fin_five (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + f 4))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem sourceZ_pos (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4) (j : Fin 5) :
    0 < sourceZ t j := by
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t <;> fin_cases j <;> norm_num [sourceZ]

theorem responseY_pos (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4) (j : Fin 5) :
    0 < responseY t j := by
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t <;> fin_cases j <;> norm_num [responseY]

theorem op_sourceZ_le (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4) (i : Fin 5) :
    (∑ j, op i j * sourceZ t j) ≤ responseY t i := by
  rw [sum_fin_five]
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t <;> fin_cases i <;>
    norm_num [op, sourceZ, responseY, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

theorem responseY_sq_sum_lt (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4) :
    (∑ i, responseY t i ^ 2) < 49/5 := by
  rw [sum_fin_five]
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t <;>
    norm_num [responseY, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

end AESPaper.SourceNumbers
