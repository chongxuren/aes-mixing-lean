import Mathlib.Data.Nat.Basic

/-!
# Dimensions of the paper's reduced return representations

The smaller-code rule retains the original representation on a tie. Its
consequences below discharge the dimensional premises of the incidence,
whole-graph and thin-code estimates from the actual return index domain.
This is integer geometry only; no analytic return cap is a hypothesis.
Frozen paper f902bb94, Section 16, reduced representation and fiber dimensions.
Constructive paper checking only; no attacks or manuscript changes.
-/

namespace AES8.PaperReturnDimensions

/-- Dimension after choosing the smaller code or its dual. -/
def reduced (n d : ℕ) : ℕ := min d (n - d)

/-- The original code is retained when the two dimensions tie. -/
def useDual (n d : ℕ) : Bool := decide (n < 2 * d)

theorem reduced_eq_choice (n d : ℕ) :
    reduced n d = if useDual n d then n - d else d := by
  by_cases h : n < 2 * d
  · simp [useDual, h, reduced] <;> omega
  · simp [useDual, h, reduced] <;> omega

theorem reduced_positive {n d : ℕ} (hd : 0 < d) (hdn : d < n) :
    0 < reduced n d := by
  unfold reduced
  omega

theorem reduced_double_le (n d : ℕ) : 2 * reduced n d ≤ n := by
  unfold reduced
  omega

/-- In the actual AES return domain, both reduced codes inject into the
middle coordinates. The borderline `i = 4, m = 3` uses integrality. -/
theorem reduced_le_middle {i m d : ℕ} (hi : i ≤ 4) (hm : 3 ≤ m) :
    reduced (i + m) d ≤ m := by
  have h := reduced_double_le (i + m) d
  omega

theorem reduced_return_domain {i m d : ℕ}
    (hi : i ≤ 4) (hm : 3 ≤ m) (hd : 0 < d) (hdn : d < i + m) :
    0 < reduced (i + m) d ∧
      2 * reduced (i + m) d ≤ i + m ∧ reduced (i + m) d ≤ m :=
  ⟨reduced_positive hd hdn, reduced_double_le _ _, reduced_le_middle hi hm⟩

/-- Number of free middle symbols after the outside coordinates are fixed. -/
def fiberDimension (outside dimension : ℕ) : ℕ :=
  dimension - min outside dimension

theorem fiberDimension_eq_sub (outside dimension : ℕ) :
    fiberDimension outside dimension = dimension - outside := by
  unfold fiberDimension
  omega

theorem fiberDimension_le_codimension {i m s : ℕ}
    (hs : s ≤ m) (hhalf : 2 * s ≤ i + m) :
    fiberDimension i s ≤ m - s := by
  unfold fiberDimension
  omega

theorem reduced_fiber_bound {i m d : ℕ} (hi : i ≤ 4) (hm : 3 ≤ m) :
    fiberDimension i (reduced (i + m) d) ≤ m - reduced (i + m) d :=
  fiberDimension_le_codimension (reduced_le_middle hi hm) (reduced_double_le _ _)

/-- Every exponent in the large-overlap formula is nonnegative, before
interpreting the half exponents as real powers. -/
theorem large_overlap_exponents {m s t a b : ℕ}
    (hs : s ≤ m) (ht : t ≤ m) (ha : a ≤ m - s) (hb : b ≤ m - t)
    (hlarge : m ≤ s + t) :
    m ≤ s + t ∧ s + t + a + b ≤ 2 * m := by
  omega

/-- This finite geometric classification justifies exhaustiveness of the
thin-code menu. It does not choose a bound by numerical optimization. -/
theorem thin_menu_complete {m s t : ℕ}
    (hm3 : 3 ≤ m) (hm4 : m ≤ 4) (hs : 0 < s) (ht : 0 < t)
    (hthin : s + t < m) :
    (m = 3 ∧ s = 1 ∧ t = 1) ∨
      (m = 4 ∧ ((s = 1 ∧ t = 1) ∨ (s = 1 ∧ t = 2) ∨
        (s = 2 ∧ t = 1))) := by
  omega

end AES8.PaperReturnDimensions
