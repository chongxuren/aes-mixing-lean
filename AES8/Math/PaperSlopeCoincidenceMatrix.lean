import AES8.Math.PaperSlopeCoincidences
import AES8.Math.PaperSlopeGroupBounds

/-! Matrix realization of the literal slope-class counts. The retained input
coordinates are the fourteen nontrivial subsets; every contraction is indexed
by one physical marked pair and one of its twenty uniform triples. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeCoincidenceMatrix
open PaperSlopeCoincidences PaperSymbolicSlopeTable PaperGroupedMatrix
set_option autoImplicit false
set_option maxRecDepth 100000

abbrev Interior := {A : Finset (Fin 4) // 1 ≤ A.card ∧ A.card ≤ 3}
def inputIndex (p : Fin 6) (k : Fin 20) : Interior := ⟨inputSet p k, input_card p k⟩

def matrix (x : ℝ) : Matrix Interior Interior ℝ := fun A B =>
  ∑ p : Fin 6, ∑ k : Fin 20, if inputSet p k = A.val then
    ∑ l : Fin 20, if slopeClass (pairType p) k = slopeClass (pairType p) l then
      if B = inputIndex p l then x^(outputDistance p k l) else 0
    else 0
  else 0

theorem matrix_action (x : ℝ) (f : Interior → ℝ) (A : Interior) :
    action (matrix x) f A =
      ∑ p : Fin 6, ∑ k : Fin 20, if inputSet p k = A.val then
        ∑ l : Fin 20, if slopeClass (pairType p) k = slopeClass (pairType p) l then
          x^(outputDistance p k l) * f (inputIndex p l) else 0
      else 0 := by
  unfold action matrix
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : inputSet p k = A.val
  · simp only [hk, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : slopeClass (pairType p) k = slopeClass (pairType p) l
    · simp [hl]
    · simp [hl]
  · simp [hk]

theorem distance_power_sum (x : ℝ) (p : Fin 6) (k l : Fin 20) :
    (∑ d : Fin 3, if outputDistance p k l = d.val then x^d.val else 0) =
      x^(outputDistance p k l) := by
  let e : Fin 3 := ⟨outputDistance p k l, Nat.lt_succ_of_le (output_distance_le p k l)⟩
  have he (d : Fin 3) : outputDistance p k l = d.val ↔ d = e := by
    simp [Fin.ext_iff, e, eq_comm]
  simp only [he]
  simp [e]

def groupedRow (x : ℝ) (A : Finset (Fin 4)) (g : Fin 2) : ℝ :=
  ∑ d : Fin 3, (count A g d : ℝ) * x^d.val

theorem groupedRow_expansion (x : ℝ) (A : Finset (Fin 4)) (g : Fin 2) :
    groupedRow x A g =
      ∑ p : Fin 6, ∑ k : Fin 20, if inputSet p k = A then
        ∑ l : Fin 20, if slopeClass (pairType p) k = slopeClass (pairType p) l ∧
          group (inputSet p l) = g then x^(outputDistance p k l) else 0
      else 0 := by
  unfold groupedRow count
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : inputSet p k = A
  · simp only [hk, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : slopeClass (pairType p) k = slopeClass (pairType p) l ∧
        group (inputSet p l) = g
    · simp only [hl.1, hl.2, true_and, if_true]
      exact distance_power_sum x p k l
    · have hh : ¬ (slopeClass (pairType p) k = slopeClass (pairType p) l ∧
          group (inputSet p l) = g ∧ outputDistance p k l = (0 : Fin 3).val) :=
        fun h => hl ⟨h.1,h.2.1⟩
      simp only [show ∀ d : Fin 3, ¬ (slopeClass (pairType p) k =
          slopeClass (pairType p) l ∧ group (inputSet p l) = g ∧
          outputDistance p k l = d.val) from fun d h => hl ⟨h.1,h.2.1⟩,
        if_false, Finset.sum_const_zero, hl]
  · simp [hk]

theorem matrix_group_row (x : ℝ) (A : Interior) (g : Fin 2) :
    (∑ B : Interior, if group B.val = g then matrix x A B else 0) =
      groupedRow x A.val g := by
  have h := matrix_action x (fun B : Interior => if group B.val = g then 1 else 0) A
  simp only [action, mul_ite, mul_one, mul_zero] at h
  rw [h, groupedRow_expansion]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · apply Finset.sum_congr rfl
    intro l _
    by_cases hc : slopeClass (pairType p) k = slopeClass (pairType p) l <;>
      by_cases hg : group (inputSet p l) = g <;> simp [hc,hg,inputIndex]
  · rfl

theorem matrix_nonneg (x : ℝ) (hx : 0 ≤ x) (A B : Interior) : 0 ≤ matrix x A B := by
  unfold matrix
  positivity

theorem matrix_entry (x : ℝ) (A B : Interior) :
    matrix x A B = ∑ p : Fin 6, ∑ k : Fin 20, ∑ l : Fin 20,
      if inputSet p k = A.val ∧ inputSet p l = B.val ∧
        slopeClass (pairType p) k = slopeClass (pairType p) l
      then x^outputDistance p k l else 0 := by
  unfold matrix
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : inputSet p k = A.val
  · simp only [hk, if_true, true_and]
    apply Finset.sum_congr rfl
    intro l _
    have hb : B = inputIndex p l ↔ inputSet p l = B.val := by
      simp [Subtype.ext_iff, inputIndex, eq_comm]
    by_cases hl : inputSet p l = B.val <;>
      by_cases hs : slopeClass (pairType p) k = slopeClass (pairType p) l <;>
      simp [hl,hs,hb]
  · simp [hk]

theorem matrix_symmetric (x : ℝ) (A B : Interior) : matrix x A B = matrix x B A := by
  rw [matrix_entry, matrix_entry]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hd : outputDistance p k l = outputDistance p l k := by
    simp [outputDistance, Finset.union_comm]
  rw [hd]
  congr 1
  simp only [and_comm, and_left_comm, eq_comm]

/-- The actual class-count matrix has the paper's two grouped row bounds. -/
theorem coincidence_group_bound :
    GroupBound (matrix (1/16)) (fun A => group A.val) (fun A => group A.val)
      PaperSlopeGroupBounds.coincidenceGroups := by
  intro A g
  rw [matrix_group_row]
  unfold groupedRow
  simp_rw [row_counts]
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hc : A.val.card = 1 ∨ A.val.card = 2 ∨ A.val.card = 3 := by
    have h := A.property
    omega
  rcases hc with hc | hc | hc <;> fin_cases g <;>
    by_cases ho : opposite A.val <;>
    norm_num [printedCount, hc, ho, group, PaperSlopeGroupBounds.coincidenceGroups,
      Fin.sum_univ_succ, h12]

end AES8.PaperSlopeCoincidenceMatrix
