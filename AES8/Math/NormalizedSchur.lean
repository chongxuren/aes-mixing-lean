/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.RectangularSchur
import AESMixing.L2Sums

/-!
# Signed kernels dominated by nonnegative collision sums

The unnormalized bound reuses the existing rectangular Schur theorem. A
normalized sum over all rows instead uses the column and total sums. These
are the two distinct estimates used for the thin-code overlap cases.
The normalization parameter is explicit; no AES or code count is assumed.
Constructive bounds only; no attacks or manuscript/predecessor changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.NormalizedSchur
open AESMixing

variable {I J : Type*} [Fintype I] [Fintype J]

theorem abs_action_le (K A : J → I → ℝ)
    (hdom : ∀ y x, |K y x| ≤ A y x) (f : I → ℝ) (y : J) :
    |action K f y| ≤ action A (fun x => |f x|) y := by
  calc
    _ ≤ ∑ x, |K y x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |K y x| * |f x| := by simp only [abs_mul]
    _ ≤ _ := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_right (hdom y x) (abs_nonneg _))

/-- Schur domination holds for arbitrary signed kernels and signed inputs. -/
theorem signed_schur_energy (K A : J → I → ℝ) (r c : ℝ) (hr : 0 ≤ r)
    (hA : ∀ y x, 0 ≤ A y x) (hdom : ∀ y x, |K y x| ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ r)
    (hcol : ∀ x, (∑ y, A y x) ≤ c) (f : I → ℝ) :
    (∑ y, action K f y ^ 2) ≤ (r*c) * ∑ x, f x ^ 2 := by
  have he : (∑ y, action K f y ^ 2) ≤
      ∑ y, action A (fun x => |f x|) y ^ 2 := by
    apply Finset.sum_le_sum
    intro y _
    have hp := (sq_le_sq₀ (abs_nonneg (action K f y))
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hA y x) (abs_nonneg _)))).mpr
        (abs_action_le K A hdom f y)
    simpa only [sq_abs, action] using hp
  exact he.trans (by
    simpa only [sq_abs] using rectangular_schur_energy A r c hr hA hrow hcol
      (fun x => |f x|))

def normalizedRowSum (K : J → I → ℝ) (m : ℕ) (x : I) : ℝ :=
  (∑ y, K y x) / Real.sqrt (m : ℝ)

/-- A normalized sum over rows uses column mass times total mass.
This bounds a signed sum; no uniformity assumption on an input error is used. -/
theorem normalized_row_energy (K A : J → I → ℝ) (c S : ℝ) (hc : 0 ≤ c)
    (hA : ∀ y x, 0 ≤ A y x) (hdom : ∀ y x, |K y x| ≤ A y x)
    (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (htotal : (∑ y, ∑ x, A y x) ≤ S) (m : ℕ) :
    (∑ x, normalizedRowSum K m x ^ 2) ≤ c * S / (m : ℝ) := by
  have hpoint (x : I) : (∑ y, K y x) ^ 2 ≤ c * ∑ y, A y x := by
    have ha : |∑ y, K y x| ≤ ∑ y, A y x :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun y _ => hdom y x))
    have hs := (sq_le_sq₀ (abs_nonneg (∑ y, K y x))
      (Finset.sum_nonneg (fun y _ => hA y x))).mpr ha
    have hcol0 : 0 ≤ ∑ y : J, A y x :=
      Finset.sum_nonneg (fun y _ => hA y x)
    have hb := mul_le_mul_of_nonneg_right (hcol x) hcol0
    calc
      _ ≤ (∑ y, A y x) ^ 2 := by simpa only [sq_abs] using hs
      _ ≤ _ := by simpa only [pow_two] using hb
  have hraw : (∑ x, (∑ y, K y x) ^ 2) ≤ c * S := by
    calc
      _ ≤ ∑ x, c * ∑ y, A y x := Finset.sum_le_sum (fun x _ => hpoint x)
      _ = c * ∑ y, ∑ x, A y x := by rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left htotal hc
  simp only [normalizedRowSum, div_pow, Real.sq_sqrt (Nat.cast_nonneg m),
    ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hraw (Nat.cast_nonneg m)

end AES8.NormalizedSchur
