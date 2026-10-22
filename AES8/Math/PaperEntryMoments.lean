import AES8.Math.PaperThinLinesRaw

/-! Reusable local-moment closure rules. Entrywise caps turn second moments
into fourth moments, and conjugate transpose exchanges row/column resources.
No AES constants, desired operator bounds, or computational premise is used. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperEntryMoments
open PaperThinLines
set_option autoImplicit false

variable {𝕜 V : Type*} [RCLike 𝕜] [Fintype V]

theorem fourth_of_entry (u : V → 𝕜) (e B : ℝ) (he : 0 ≤ e)
    (hentry : ∀ x, ‖u x‖ ≤ e) (hsecond : (∑ x, ‖u x‖ ^ 2) ≤ B) :
    (∑ x, ‖u x‖ ^ 4) ≤ e ^ 2 * B := by
  calc
    _ ≤ ∑ x, e ^ 2 * ‖u x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      have hx := (sq_le_sq₀ (norm_nonneg (u x)) he).mpr (hentry x)
      calc
        ‖u x‖ ^ 4 = ‖u x‖ ^ 2 * ‖u x‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    _ = e ^ 2 * ∑ x, ‖u x‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (sq_nonneg e)

theorem of_entry {n : ℕ} (T : Fin n → V → V → 𝕜) (δ τ e : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (he : 0 ≤ e)
    (hentry : ∀ j y x, ‖T j y x‖ ≤ e)
    (hrow : ∀ j y, (∑ x, ‖T j y x‖ ^ 2) ≤ δ)
    (hcol : ∀ j x, (∑ y, ‖T j y x‖ ^ 2) ≤ δ)
    (htotal : ∀ j, (∑ y, ∑ x, ‖T j y x‖ ^ 2) ≤ τ) :
    EntryMoments T δ τ e e := by
  refine ⟨hδ, hτ, he, he, hrow, hcol, htotal, ?_, ?_, ?_⟩
  · intro j y
    exact fourth_of_entry _ e δ he (hentry j y) (hrow j y)
  · intro j x
    exact fourth_of_entry _ e δ he (fun y => hentry j y x) (hcol j x)
  · intro j
    calc
      _ ≤ ∑ y, e ^ 2 * ∑ x, ‖T j y x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        exact fourth_of_entry _ e _ he (hentry j y) le_rfl
      _ = e ^ 2 * ∑ y, ∑ x, ‖T j y x‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (htotal j) (sq_nonneg e)

theorem conjTranspose {n : ℕ} (T : Fin n → V → V → 𝕜) (δ τ r s : ℝ)
    (h : EntryMoments T δ τ r s) :
    EntryMoments (fun j => Matrix.conjTranspose (T j)) δ τ r s := by
  refine ⟨h.delta_nonneg, h.tau_nonneg, h.rowScale_nonneg, h.totalScale_nonneg,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j y
    simpa only [Matrix.conjTranspose_apply, norm_star] using h.col_second j y
  · intro j x
    simpa only [Matrix.conjTranspose_apply, norm_star] using h.row_second j x
  · intro j
    simp only [Matrix.conjTranspose_apply, norm_star]
    rw [Finset.sum_comm]
    exact h.total_second j
  · intro j y
    simpa only [Matrix.conjTranspose_apply, norm_star] using h.col_fourth j y
  · intro j x
    simpa only [Matrix.conjTranspose_apply, norm_star] using h.row_fourth j x
  · intro j
    simp only [Matrix.conjTranspose_apply, norm_star]
    rw [Finset.sum_comm]
    exact h.total_fourth j

end AES8.PaperEntryMoments
