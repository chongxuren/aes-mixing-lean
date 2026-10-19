import AESMixing.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
Exact finite-law identities underlying whitening and adaptive second queries.
Their identification with the concrete cipher experiment remains separate.
-/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

def uniformFirst (p : ι → ℝ) : κ × ι → ℝ :=
  fun x => p x.2 / (Fintype.card κ : ℝ)

theorem tv_uniformFirst (p q : ι → ℝ) :
    tv (uniformFirst (κ := κ) p) (uniformFirst (κ := κ) q) = tv p q := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold tv uniformFirst
  simp only [Fintype.sum_prod_type, ← sub_div, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card κ by positivity), ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

def uniformRows (p : κ → ι → ℝ) : κ × ι → ℝ :=
  fun x => p x.1 x.2 / (Fintype.card κ : ℝ)

/-- Averaging conditional second-answer bounds loses no factor. -/
theorem tv_uniformRows_le (p q : κ → ι → ℝ) (eps : ℝ)
    (h : ∀ y, tv (p y) (q y) ≤ eps) :
    tv (uniformRows p) (uniformRows q) ≤ eps := by
  have hn : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hs : (∑ y, tv (p y) (q y)) ≤ (Fintype.card κ : ℝ) * eps := by
    calc
      (∑ y, tv (p y) (q y)) ≤ ∑ _ : κ, eps := Finset.sum_le_sum (fun y _ => h y)
      _ = (Fintype.card κ : ℝ) * eps := by simp
  have hid : tv (uniformRows p) (uniformRows q) =
      (∑ y, tv (p y) (q y)) / (Fintype.card κ : ℝ) := by
    unfold tv uniformRows
    simp only [Fintype.sum_prod_type, ← sub_div, abs_div,
      abs_of_nonneg (le_of_lt hn), ← Finset.sum_div]
    ring
  rw [hid]
  apply (div_le_iff₀ hn).mpr
  simpa [mul_comm] using hs

end AESMixing
