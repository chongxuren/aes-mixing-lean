import AESPaper.ActivityMDSCounts
import AESMixing.WeightedRectangularSchur

/-!
# Exact four-dimensional activity comparison for the fixed v9 target

The coefficients are the exact MDS support counts with the nonzero stationary
coefficient subtracted. This module proves their matrix energy bound. The
identification with the actual centered AES activity operator is a separate
obligation; it is not an assumption silently added to this certificate.
Only exact real/rational arithmetic and kernel-checked proofs are used.
-/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AESPaper.ActivityMatrix
open AESMixing
open AESPaper.ActivityMDSCounts

def q : ℝ := 2^32

def mass (a : Fin 4) : ℝ := (Nat.choose 4 (a.val+1) : ℝ) * (q-1)^(a.val+1)

def coefficient (a b : Fin 4) : ℝ :=
  supportCount q (a.val+b.val+2) / (q-1)^(a.val+b.val+2) - 1/(q^4-1)

def matrix (a b : Fin 4) : ℝ := coefficient a b * Real.sqrt (mass a * mass b)

def envelope : Fin 4 → Fin 4 → ℝ :=
  ![![1/1000000, 1/10000, 4, 1/1000],
    ![1/10000, 6, 1/1000, 1/1000000],
    ![4, 1/1000, 1/1000000, 1/1000000],
    ![1/1000, 1/1000000, 1/1000000, 1/1000000]]

theorem q_pos : 0 < q := by norm_num [q]
theorem mass_pos (a : Fin 4) : 0 < mass a := by
  fin_cases a <;> norm_num [mass, q, Nat.choose]

theorem envelope_nonneg (a b : Fin 4) : 0 ≤ envelope a b := by
  fin_cases a <;> fin_cases b <;> norm_num [envelope]

theorem envelope_symmetric (a b : Fin 4) : envelope a b = envelope b a := by
  fin_cases a <;> fin_cases b <;> norm_num [envelope]

theorem envelope_row (a : Fin 4) : (∑ b, envelope a b) ≤ 601/100 := by
  fin_cases a <;> norm_num [envelope, Fin.sum_univ_succ]

theorem envelope_col (b : Fin 4) : (∑ a, envelope a b) ≤ 601/100 := by
  simp_rw [envelope_symmetric _ b]
  exact envelope_row b

/-- Sixteen rational squared-entry certificates at q=2^32. -/
theorem squared_entry_certificate (a b : Fin 4) :
    q^4 * coefficient a b^2 * mass a * mass b < envelope a b^2 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [q, coefficient, mass, envelope, supportCount, Finset.sum_range_succ, Nat.choose]

theorem scaled_entry_abs (a b : Fin 4) : q^2 * |matrix a b| ≤ envelope a b := by
  have hsq := squared_entry_certificate a b
  have hm : 0 ≤ mass a * mass b := le_of_lt (mul_pos (mass_pos a) (mass_pos b))
  have he := envelope_nonneg a b
  have hroot := Real.sq_sqrt hm
  have habs : |matrix a b|^2 = coefficient a b^2 * (mass a * mass b) := by
    rw [sq_abs, matrix, mul_pow, hroot]
  have hp : 0 ≤ q^2 * |matrix a b| := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hs : (q^2 * |matrix a b|)^2 < envelope a b^2 := by
    calc
      _ = q^4 * coefficient a b^2 * mass a * mass b := by
        rw [mul_pow, habs]
        ring
      _ < _ := hsq
  nlinarith [sq_nonneg (q^2 * |matrix a b| - envelope a b)]

/-- Signed domination followed by a nonnegative row/column Schur estimate. -/
theorem signed_schur_energy {I J : Type*} [Fintype I] [Fintype J]
    (K A : J → I → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ y x, 0 ≤ A y x) (hdom : ∀ y x, |K y x| ≤ A y x)
    (hrow : ∀ y, (∑ x, A y x) ≤ c) (hcol : ∀ x, (∑ y, A y x) ≤ c)
    (f : I → ℝ) :
    (∑ y, action K f y^2) ≤ c^2 * ∑ x, f x^2 := by
  have hp (y : J) : |action K f y| ≤ action A (fun x => |f x|) y := by
    calc
      _ ≤ ∑ x, |K y x * f x| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, A y x * |f x| := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hdom y x) (abs_nonneg _)
  have hs := weighted_rectangular_schur_energy A (fun _ => 1) (fun _ => 1) c hc hA
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun y => by simpa using hrow y) (fun x => by simpa using hcol x) (fun x => |f x|)
  simp only [sq_abs] at hs
  apply le_trans (Finset.sum_le_sum (fun y _ => ?_)) hs
  have hh := hp y
  have hn := abs_nonneg (action K f y)
  have habs := sq_abs (action K f y)
  nlinarith

theorem matrix_energy (f : Fin 4 → ℝ) :
    (∑ a, action matrix f a^2) ≤ ((601/100)/q^2)^2 * ∑ b, f b^2 := by
  apply signed_schur_energy matrix (fun a b => envelope a b / q^2)
      ((601/100)/q^2) (by positivity)
  · intro a b
    exact div_nonneg (envelope_nonneg a b) (sq_nonneg _)
  · intro a b
    apply (le_div_iff₀ (pow_pos q_pos 2)).mpr
    simpa only [mul_comm] using scaled_entry_abs a b
  · intro a
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (envelope_row a) (sq_nonneg _)
  · intro b
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (envelope_col b) (sq_nonneg _)

end AESPaper.ActivityMatrix
