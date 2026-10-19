import AESMixing.WordMDS
import AESPaper.RareActivity

/-!
Exact finite counts for the all-active word cell. The proof counts the product
of four sets of nonzero words; it never enumerates the AES state space.
These counts give only counting-measure norm conversion constants. They do
not assert that an AES law has the constant-cell or zero-sum properties.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AESPaper.WordCells
open AESMixing AESMixing.AES

/-- The word-activity cell with all four words nonzero. -/
def allActive : Finset WordState :=
  Finset.univ.filter (fun x => ∀ i, x i ≠ 0)

@[simp] theorem mem_allActive (x : WordState) :
    x ∈ allActive ↔ ∀ i, x i ≠ 0 := by
  simp [allActive]

@[simp] theorem mem_allActive_compl (x : WordState) :
    x ∈ allActiveᶜ ↔ ∃ i, x i = 0 := by
  classical
  simp [allActive, not_forall]

theorem wordState_card : Fintype.card WordState = (2^32)^4 := by
  change Fintype.card (Fin 4 → Word) = _
  rw [Fintype.card_fun, Fintype.card_fin, word_card]

theorem allActive_card : allActive.card = (2^32-1)^4 := by
  have hproduct : allActive = Fintype.piFinset
      (fun _ : Fin 4 => (Finset.univ : Finset Word).erase 0) := by
    ext x
    simp [allActive]
  rw [hproduct, Fintype.card_piFinset_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Word)), Finset.card_univ, word_card]

theorem allActive_compl_card :
    (allActiveᶜ).card = (2^32)^4 - (2^32-1)^4 := by
  rw [Finset.card_compl, wordState_card, allActive_card]

/-- The usual four-coordinate union bound, obtained from the exact count. -/
theorem allActive_compl_card_le :
    (allActiveᶜ).card ≤ 4*(2^32)^3 := by
  rw [allActive_compl_card]
  norm_num

theorem allActive_compl_card_le_real_union :
    ((allActiveᶜ).card : ℝ) ≤ 4*((2:ℝ)^32)^3 := by
  exact_mod_cast allActive_compl_card_le

/-- Square form used by the activity-cell Cauchy--Schwarz estimate. -/
theorem allActive_compl_card_le_real :
    ((allActiveᶜ).card : ℝ) ≤ ((2:ℝ)^49)^2 := by
  calc
    _ ≤ 4*((2:ℝ)^32)^3 := allActive_compl_card_le_real_union
    _ = _ := by norm_num

/-- The full physical state count, in the square form for ordinary l1/l2. -/
theorem state_card_real_sq :
    (Fintype.card State : ℝ) = ((2:ℝ)^64)^2 := by
  rw [state_card]
  norm_num

theorem ordinary_l1 (f : State → ℝ) :
    RareActivity.l1 f ≤ (2:ℝ)^64 * l2 f := by
  exact RareActivity.l1_le_of_card f ((2:ℝ)^64) (by positivity)
    state_card_real_sq.le

/-- Constant-cell cancellation removes the full-state coefficient. The
two structural hypotheses must be supplied by the caller. -/
theorem activity_l1 (f : WordState → ℝ) (c : ℝ)
    (hconst : ∀ x ∈ allActive, f x = c) (hzero : (∑ x, f x) = 0) :
    RareActivity.l1 f ≤ (2:ℝ)^50 * l2 f := by
  have h := RareActivity.rare_cell_l1 allActive f c ((2:ℝ)^49)
    hconst hzero (by positivity) allActive_compl_card_le_real
  simpa only [show (2:ℝ)*(2:ℝ)^49 = (2:ℝ)^50 by norm_num] using h

end AESPaper.WordCells
