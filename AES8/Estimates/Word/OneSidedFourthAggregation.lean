/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Word.OneSidedWordEnergy

/-!
# One-sided fourth sums from separate ordinary and exceptional entry resources

The finite-sum lemma charges the exceptional entries once and uses the
pointwise cap only on their complement. The actual one-sided word corollaries
then reuse the proved row, column and total second moments. Their explicit
entry/exception premises remain to be instantiated by the byte/MDS argument;
this file does not assert those missing actual AES resources.

 Constructive
proof work only; no attacks, local execution or manuscript/predecessor edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.OneSidedFourthAggregation
open AESMixing AESMixing.AES
open AES8.OneSidedWordEnergy

section Generic
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- The exceptional fourth sum is supplied separately; no entry cap is used
on that set. The full second sum is a harmless upper bound for its complement. -/
theorem fourth_sum_le_of_exceptional (u : I → ℝ) (s : Finset I) (A E : ℝ)
    (hA : 0 ≤ A) (hentry : ∀ i, i ∉ s → |u i| ≤ A)
    (hexception : (∑ i ∈ s, u i ^ 4) ≤ E) :
    (∑ i, u i ^ 4) ≤ A ^ 2 * (∑ i, u i ^ 2) + E := by
  have hout : (∑ i ∈ sᶜ, u i ^ 4) ≤ A ^ 2 * (∑ i, u i ^ 2) := by
    calc
      _ ≤ ∑ i ∈ sᶜ, A ^ 2 * u i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∉ s := Finset.mem_compl.mp hi
        have hs : u i ^ 2 ≤ A ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (u i)) hA).mpr (hentry i hi')
        have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (u i))
        nlinarith only [hm]
      _ = A ^ 2 * ∑ i ∈ sᶜ, u i ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ sᶜ)
          (fun _ _ _ => sq_nonneg _)) (sq_nonneg A)
  have hsplit := Finset.sum_add_sum_compl s (fun i => u i ^ 4)
  linarith only [hexception, hout, hsplit]

/-- Summing the same row split keeps the exceptional total explicit. -/
theorem matrix_fourth_le_of_exceptional (T : J → I → ℝ)
    (s : J → Finset I) (A : ℝ) (hA : 0 ≤ A)
    (hentry : ∀ j i, i ∉ s j → |T j i| ≤ A) :
    (∑ j, ∑ i, T j i ^ 4) ≤
      A ^ 2 * (∑ j, ∑ i, T j i ^ 2) + ∑ j, ∑ i ∈ s j, T j i ^ 4 := by
  calc
    _ ≤ ∑ j, (A ^ 2 * (∑ i, T j i ^ 2) + ∑ i ∈ s j, T j i ^ 4) := by
      apply Finset.sum_le_sum
      intro j _
      exact fourth_sum_le_of_exceptional (T j) (s j) A _ hA (hentry j) le_rfl
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end Generic

/-- A row meets at most four exceptional byte-position blocks. This theorem
retains the resulting exceptional-sum premise, without asserting the blocks. -/
theorem row_fourth_lt (adjoint : Bool) (y : AES.Word) (s : Finset AES.Word)
    (hentry : ∀ x, x ∉ s →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ))
    (hexception : (∑ x ∈ s, rightMixed adjoint y x ^ 4) ≤
      (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ)) :
    (∑ x, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  calc
    _ ≤ (1152 / 4294967296 : ℝ) ^ 2 *
        (∑ x, rightMixed adjoint y x ^ 2) +
        (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) :=
      fourth_sum_le_of_exceptional _ s _ _ (by norm_num) hentry hexception
    _ < (1152 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) +
        (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
      have hh := mul_lt_mul_of_pos_left (row_energy_lt adjoint y)
        (by norm_num : (0 : ℝ) < (1152 / 4294967296 : ℝ) ^ 2)
      linarith only [hh]
    _ < _ := by norm_num

/-- The column argument has the same constant, using the proved column energy. -/
theorem column_fourth_lt (adjoint : Bool) (x : AES.Word) (s : Finset AES.Word)
    (hentry : ∀ y, y ∉ s →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ))
    (hexception : (∑ y ∈ s, rightMixed adjoint y x ^ 4) ≤
      (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ)) :
    (∑ y, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  calc
    _ ≤ (1152 / 4294967296 : ℝ) ^ 2 *
        (∑ y, rightMixed adjoint y x ^ 2) +
        (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) :=
      fourth_sum_le_of_exceptional _ s _ _ (by norm_num) hentry hexception
    _ < (1152 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) +
        (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
      have hh := mul_lt_mul_of_pos_left (column_energy_lt adjoint x)
        (by norm_num : (0 : ℝ) < (1152 / 4294967296 : ℝ) ^ 2)
      linarith only [hh]
    _ < _ := by norm_num

/-- The total exceptional resource charges 1020 possible one-active-byte rows,
each meeting four blocks; its actual support/count proof is a separate input. -/
theorem total_fourth_lt (adjoint : Bool) (s : AES.Word → Finset AES.Word)
    (hentry : ∀ y x, x ∉ s y →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ))
    (hexception : (∑ y, ∑ x ∈ s y, rightMixed adjoint y x ^ 4) ≤
      (1020 * (4 * 25 * 2 ^ 44) / 4294967296 ^ 4 : ℝ)) :
    (∑ y, ∑ x, rightMixed adjoint y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) := by
  calc
    _ ≤ (1152 / 4294967296 : ℝ) ^ 2 *
        (∑ y, ∑ x, rightMixed adjoint y x ^ 2) +
        ∑ y, ∑ x ∈ s y, rightMixed adjoint y x ^ 4 :=
      matrix_fourth_le_of_exceptional _ s _ (by norm_num) hentry
    _ ≤ (1152 / 4294967296 : ℝ) ^ 2 *
        (∑ y, ∑ x, rightMixed adjoint y x ^ 2) +
        (1020 * (4 * 25 * 2 ^ 44) / 4294967296 ^ 4 : ℝ) :=
      add_le_add le_rfl hexception
    _ < (1152 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) +
        (1020 * (4 * 25 * 2 ^ 44) / 4294967296 ^ 4 : ℝ) := by
      have hh := mul_lt_mul_of_pos_left (trace_lt adjoint)
        (by norm_num : (0 : ℝ) < (1152 / 4294967296 : ℝ) ^ 2)
      linarith only [hh]
    _ < _ := by norm_num

end AES8.OneSidedFourthAggregation
