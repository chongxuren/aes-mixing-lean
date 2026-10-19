import AESPaper.TernaryDegree
import AESPaper.StartingWord
import AESPaper.WordDamping
import AESPaper.ManySourceMarginal
import Mathlib.Data.Rat.BigOperators

/-!
# Finite scalar budgets for positive residual degrees

The eighty-one literal J/Z/R patterns are grouped by the existing residual
index, which counts only R labels. Bias labels have their own count. The
finite certificate below evaluates rational budgets only; it does not assert
that any actual AES term satisfies its assigned budget.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators

namespace AESPaper.MixedDegreeBudgets
open AESPaper.TernaryDegree (residualIndex)
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)

/-- Only label one is a bias factor; residual labels are counted separately. -/
def biasCount (a : Fin 4 → Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin 4 => a i = 1)).card

/-- Small label-only certificate, used before any rational calculation. -/
theorem biasCount_four : ∀ a : Fin 4 → Fin 3,
    biasCount a = (if a 0 = 1 then 1 else 0) + (if a 1 = 1 then 1 else 0) +
      (if a 2 = 1 then 1 else 0) + (if a 3 = 1 then 1 else 0) := by
  decide

theorem residualCount_four : ∀ a : Fin 4 → Fin 3,
    (residualIndex a).val =
      (if a 0 = 2 then 1 else 0) + (if a 1 = 2 then 1 else 0) +
      (if a 2 = 2 then 1 else 0) + (if a 3 = 2 then 1 else 0) := by
  decide

/-- Enumerate functions by their four coordinates using the checked tuple
equivalence. This structural identity has no numerical approximation. -/
theorem sum_patterns (f : (Fin 4 → Fin 3) → ℚ) :
    (∑ a : Fin 4 → Fin 3, f a) =
      ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3, ∑ a3 : Fin 3,
        f (fun i : Fin 4 => if i = 0 then a0 else if i = 1 then a1
          else if i = 2 then a2 else a3) := by
  rw [← (ManySourceMarginal.fourTupleEquiv (Fin 3)).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

def biasIndex (a : Fin 4 → Fin 3) : Fin 5 :=
  ⟨biasCount a, Nat.lt_succ_of_le
    ((Finset.card_filter_le _ _).trans_eq (by simp))⟩

def patternClass (a : Fin 4 → Fin 3) : Fin 5 × Fin 5 :=
  (residualIndex a, biasIndex a)

/-- The finite label histogram contains no rational arithmetic. -/
theorem pattern_count : ∀ r z : Fin 5,
    (Finset.univ.filter (fun a : Fin 4 → Fin 3 => patternClass a = (r, z))).card =
      Nat.choose 4 r.val * Nat.choose (4 - r.val) z.val := by
  decide

theorem sum_by_counts (f : Fin 5 × Fin 5 → ℚ) :
    (∑ a : Fin 4 → Fin 3, f (patternClass a)) =
      ∑ r : Fin 5, ∑ z : Fin 5,
        ((Nat.choose 4 r.val * Nat.choose (4 - r.val) z.val : ℕ) : ℚ) *
          f (r, z) := by
  rw [← Finset.sum_fiberwise' Finset.univ patternClass f,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_const, nsmul_eq_mul, pattern_count]

/-- Restrict equality simplification to degree labels; do not unfold arbitrary
finite-index equalities inside coordinate functions. -/
theorem degree_eq_iff_val (r s : Fin 5) : r = s ↔ r.val = s.val := Fin.ext_iff

def B : ℝ := 441 / (q - 1)

def rationalQ : ℚ := 4294967296
def rationalNu : ℚ := 21 / 131072
def rationalB : ℚ := 441 / (rationalQ - 1)

/-- Exact rational version used solely for the finite arithmetic certificate. -/
def rationalBudget (a : Fin 4 → Fin 3) : ℚ :=
  if residualIndex a = 0 then 0
  else if biasCount a = 0 then
    if residualIndex a = 1 then 441 / 100
    else rationalQ * (6 / 5) ^ 4 * rationalNu ^ 4
  else rationalQ * (6 / 5) ^ 4 * rationalNu ^ 2 * rationalB ^ biasCount a

def rationalCoefficient (r z : Fin 5) : ℚ :=
  if r.val = 0 then 0
  else if z.val = 0 then
    if r.val = 1 then 441 / 100
    else rationalQ * (6 / 5) ^ 4 * rationalNu ^ 4
  else rationalQ * (6 / 5) ^ 4 * rationalNu ^ 2 * rationalB ^ z.val

theorem rationalBudget_eq_coefficient (a : Fin 4 → Fin 3) :
    rationalBudget a = rationalCoefficient (residualIndex a) (biasIndex a) := by
  unfold rationalBudget rationalCoefficient
  have h0 : residualIndex a = 0 ↔ (residualIndex a).val = 0 := Fin.ext_iff
  have h1 : residualIndex a = 1 ↔ (residualIndex a).val = 1 := Fin.ext_iff
  simp only [h0, h1, biasIndex]

/-- Budget for `q^5` times a literal pattern's squared energy. -/
def budget (a : Fin 4 → Fin 3) : ℝ := (rationalBudget a : ℝ)

/-- The rational representation has exactly the intended real coefficients. -/
theorem budget_formula (a : Fin 4 → Fin 3) :
    budget a =
      if residualIndex a = 0 then 0
      else if biasCount a = 0 then
        if residualIndex a = 1 then 441 / 100
        else q * (6 / 5) ^ 4 * nu ^ 4
      else q * (6 / 5) ^ 4 * nu ^ 2 * B ^ biasCount a := by
  unfold budget rationalBudget
  split_ifs <;>
    norm_num [rationalQ, rationalNu, rationalB, q, nu, B]

theorem budget_zero (a : Fin 4 → Fin 3) (hr : residualIndex a = 0) :
    budget a = 0 := by
  rw [budget_formula]
  simp [hr]

theorem budget_pure_one (a : Fin 4 → Fin 3)
    (hr : residualIndex a = 1) (hz : biasCount a = 0) :
    budget a = 441 / 100 := by
  rw [budget_formula]
  simp [hr, hz]

theorem budget_pure_many (a : Fin 4 → Fin 3)
    (hr : 2 ≤ (residualIndex a).val) (hz : biasCount a = 0) :
    budget a = q * (6 / 5) ^ 4 * nu ^ 4 := by
  have h0 : residualIndex a ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have h1 : residualIndex a ≠ 1 := by
    intro h
    rw [h] at hr
    norm_num at hr
  rw [budget_formula]
  simp [h0, h1, hz]

theorem budget_mixed (a : Fin 4 → Fin 3)
    (hr : residualIndex a ≠ 0) (hz : biasCount a ≠ 0) :
    budget a = q * (6 / 5) ^ 4 * nu ^ 2 * B ^ biasCount a := by
  rw [budget_formula]
  simp [hr, hz]

def rationalDegreeBudget (j : Fin 5) : ℚ :=
  ∑ a : Fin 4 → Fin 3, if residualIndex a = j then rationalBudget a else 0

def degreeBudget (j : Fin 5) : ℝ :=
  ∑ a : Fin 4 → Fin 3, if residualIndex a = j then budget a else 0

/-- Collapse the degree filter before performing the five remaining scalar
calculations. The degree equality is handled by a single-sum identity. -/
theorem rationalDegreeBudget_eq_sum (j : Fin 5) :
    rationalDegreeBudget j =
      ∑ z : Fin 5,
        ((Nat.choose 4 j.val * Nat.choose (4 - j.val) z.val : ℕ) : ℚ) *
          rationalCoefficient j z := by
  have h : rationalDegreeBudget j =
      ∑ a : Fin 4 → Fin 3,
        (fun p : Fin 5 × Fin 5 =>
          if p.1 = j then rationalCoefficient p.1 p.2 else 0) (patternClass a) := by
    simp only [rationalDegreeBudget, patternClass, rationalBudget_eq_coefficient]
  rw [h, sum_by_counts (fun p : Fin 5 × Fin 5 =>
    if p.1 = j then rationalCoefficient p.1 p.2 else 0)]
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
  · intro r _ hr
    simp only [if_neg hr, mul_zero, Finset.sum_const_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Exhaustive exact arithmetic over the 81 ternary patterns; no AES law or
analytic inequality is part of this certificate. -/
theorem rationalDegreeBudget_values : ∀ j : Fin 5,
    rationalDegreeBudget j =
      if j.val = 0 then 0
      else if j.val = 1 then
        32352016276717871368811593025133 / 1833985242104724661696763828125
      else if j.val = 2 then
        871772559468024859817156523 / 2750977863797598939250688000000
      else if j.val = 3 then
        112764087178354773 / 960767920282009600000
      else 15752961 / 2684354560000 := by
  classical
  intro j
  rw [rationalDegreeBudget_eq_sum]
  fin_cases j <;> norm_num [Fin.sum_univ_succ, rationalCoefficient,
    rationalQ, rationalNu, rationalB, Nat.choose]

theorem degreeBudget_eq_cast (j : Fin 5) :
    degreeBudget j = (rationalDegreeBudget j : ℝ) := by
  unfold degreeBudget rationalDegreeBudget
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : residualIndex a = j <;> simp [ha, budget]

theorem degreeBudget_one_lt : degreeBudget 1 < 17641 / 1000 := by
  rw [degreeBudget_eq_cast, rationalDegreeBudget_values]
  change ((32352016276717871368811593025133 /
    1833985242104724661696763828125 : ℚ) : ℝ) < 17641 / 1000
  norm_num

theorem degreeBudget_two_lt : degreeBudget 2 < 1 / 1000 := by
  rw [degreeBudget_eq_cast, rationalDegreeBudget_values]
  change ((871772559468024859817156523 /
    2750977863797598939250688000000 : ℚ) : ℝ) < 1 / 1000
  norm_num

theorem degreeBudget_three_lt : degreeBudget 3 < 1 / 1000 := by
  rw [degreeBudget_eq_cast, rationalDegreeBudget_values]
  change ((112764087178354773 / 960767920282009600000 : ℚ) : ℝ) < 1 / 1000
  norm_num

theorem degreeBudget_four_lt : degreeBudget 4 < 1 / 6400 := by
  rw [degreeBudget_eq_cast, rationalDegreeBudget_values]
  change ((15752961 / 2684354560000 : ℚ) : ℝ) < 1 / 6400
  norm_num

/-- All positive-degree scalar sums fit strictly below the manuscript caps. -/
theorem degreeBudget_lt_initialProfile (j : Fin 5) (hj : j ≠ 0) :
    degreeBudget j < AESPaper.initialProfile j ^ 2 := by
  fin_cases j
  · exact (hj rfl).elim
  · exact lt_trans degreeBudget_one_lt (by norm_num [AESPaper.initialProfile])
  · exact lt_trans degreeBudget_two_lt (by norm_num [AESPaper.initialProfile])
  · exact lt_trans degreeBudget_three_lt (by norm_num [AESPaper.initialProfile])
  · convert degreeBudget_four_lt using 1 <;> norm_num [AESPaper.initialProfile] <;> congr 1

/-- Scalar aggregation keeps each required per-pattern bound as a premise. -/
theorem sum_le_degreeBudget (e : (Fin 4 → Fin 3) → ℝ) (j : Fin 5)
    (he : ∀ a, residualIndex a = j → e a ≤ budget a) :
    (∑ a : Fin 4 → Fin 3, if residualIndex a = j then e a else 0) ≤
      degreeBudget j := by
  unfold degreeBudget
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : residualIndex a = j
  · simp only [if_pos ha]
    exact he a ha
  · simp [ha]

theorem sum_lt_initialProfile (e : (Fin 4 → Fin 3) → ℝ)
    (j : Fin 5) (hj : j ≠ 0)
    (he : ∀ a, residualIndex a = j → e a ≤ budget a) :
    (∑ a : Fin 4 → Fin 3, if residualIndex a = j then e a else 0) <
      AESPaper.initialProfile j ^ 2 :=
  (sum_le_degreeBudget e j he).trans_lt (degreeBudget_lt_initialProfile j hj)

/-- Convenience form for the actual degree-energy identity, once its literal
term bounds have been proved by the caller. -/
theorem scaled_sum_lt_initialProfile (e : (Fin 4 → Fin 3) → ℝ)
    (j : Fin 5) (hj : j ≠ 0)
    (he : ∀ a, residualIndex a = j → q ^ 5 * e a ≤ budget a) :
    q ^ 5 * (∑ a : Fin 4 → Fin 3, if residualIndex a = j then e a else 0) <
      AESPaper.initialProfile j ^ 2 := by
  simpa only [Finset.mul_sum, mul_ite, mul_zero] using
    sum_lt_initialProfile (fun a => q ^ 5 * e a) j hj he

end AESPaper.MixedDegreeBudgets
