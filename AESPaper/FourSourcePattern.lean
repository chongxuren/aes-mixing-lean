import AESPaper.CappedSourceGram
import AESMixing.FiveDegree

/-!
# Four-coordinate mixed common-source Gram patterns

A residual bit retains its own Gram factor, whereas an activity bit supplies
the same nonnegative scalar `c`. The source label remains common to all four
positions. For degrees two through four, selecting the marked factors reduces
the signed double sum to `CappedSourceGram.weighted_product_bound` with width
two, three, or four. No independence, Gram equality, or sign restriction on
the source weights is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators Matrix

namespace AESPaper.FourSourcePattern
open AESMixing

section Scalar
variable {X : Type*} [Fintype X]

/-- Factor a nonnegative constant out of a selected common-source product.
The selection need not be injective; callers establish the product identity. -/
theorem selected_bound (n k : ℕ) (e : Fin (n+2) → Fin 4)
    (G : Fin 4 → X → X → ℝ) (mu : X → ℝ) (p tau delta c : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i x z, |G i x z| ≤ delta)
    (hmoment : ∀ i, (∑ x, ∑ z, G i x z ^ 2) ≤ tau ^ 2)
    (b : Fin 4 → Bool)
    (hprod : ∀ x z, (∏ i, if b i then G i x z else c) =
      (∏ i, G (e i) x z) * c ^ k) :
    (∑ x, ∑ z, mu x * mu z * ∏ i, if b i then G i x z else c) ≤
      p ^ 2 * tau ^ 2 * delta ^ n * c ^ k := by
  have h := CappedSourceGram.weighted_product_bound n
    (fun i x z => G (e i) x z) mu p tau delta hp hd hmu
    (fun i x z => hentry (e i) x z) (fun i => hmoment (e i))
  calc
    _ = (∑ x, ∑ z, mu x * mu z * ∏ i, G (e i) x z) * c ^ k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      rw [hprod x z]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (pow_nonneg hc k)

/-- The sixteen Boolean patterns have their literal four-bit degree. -/
theorem residualDegree_four_bits : ∀ b : Fin 4 → Bool,
    residualDegree b =
      (if b 0 then 1 else 0) + (if b 1 then 1 else 0) +
      (if b 2 then 1 else 0) + (if b 3 then 1 else 0) := by decide

/-- The genuine residual-position patterns have binomial multiplicities. -/
theorem degree_pattern_count : ∀ j : Fin 5,
    (Finset.univ.filter (fun b : Fin 4 → Bool => degreeIndex b = j)).card =
      Nat.choose 4 j.val := by decide

/-- Grouping a scalar bound by degree introduces precisely its multiplicity. -/
theorem degree_constant_sum (j : Fin 5) (r : ℝ) :
    (∑ b : Fin 4 → Bool, if degreeIndex b = j then r else 0) =
      (Nat.choose 4 j.val : ℝ) * r := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, degree_pattern_count]

theorem degree_indicator_sum (j : Fin 5) :
    (∑ b : Fin 4 → Bool, if degreeIndex b = j then (1 : ℝ) else 0) =
      (Nat.choose 4 j.val : ℝ) := by
  simpa only [mul_one] using degree_constant_sum j 1

/-- A degree-two, degree-three, or degree-four mixed Gram pattern retains two
second-moment factors and caps only the remaining residual positions. -/
theorem mixed_bound (G : Fin 4 → X → X → ℝ) (mu : X → ℝ)
    (p tau delta c : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i x z, |G i x z| ≤ delta)
    (hmoment : ∀ i, (∑ x, ∑ z, G i x z ^ 2) ≤ tau ^ 2)
    (b : Fin 4 → Bool) (hb : 2 ≤ residualDegree b) :
    (∑ x, ∑ z, mu x * mu z * ∏ i, if b i then G i x z else c) ≤
      p ^ 2 * tau ^ 2 * delta ^ (residualDegree b - 2) *
        c ^ (4 - residualDegree b) := by
  have hdeg := residualDegree_four_bits b
  cases h0 : b 0 <;> cases h1 : b 1 <;>
    cases h2 : b 2 <;> cases h3 : b 3
  all_goals norm_num [h0, h1, h2, h3] at hdeg
  all_goals rw [hdeg] at hb ⊢
  -- Close the five excluded degrees before simplifying the surviving targets.
  -- A combined `at hb ⊢` continues after a contradictory hypothesis closes a goal.
  all_goals norm_num at hb
  all_goals norm_num
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![2, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![1, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![1, 2] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_one] using
      selected_bound 1 1 ![1, 2, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![0, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![0, 2] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_one] using
      selected_bound 1 1 ![0, 2, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 0 2 ![0, 1] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_one] using
      selected_bound 1 1 ![0, 1, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_one] using
      selected_bound 1 1 ![0, 1, 2] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)
  · simpa only [pow_zero, mul_one] using
      selected_bound 2 0 ![0, 1, 2, 3] G mu p tau delta c hp hd hc hmu hentry hmoment b
        (by intro x z; simp [Fin.prod_univ_succ, h0, h1, h2, h3] <;> ring)

end Scalar
end AESPaper.FourSourcePattern
