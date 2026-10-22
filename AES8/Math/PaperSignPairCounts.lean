import AESMixing.Finite

/-!
Symbolic counting for two functions valued in {1,-1}. This leaf owns only
the four-cell algebra. Byte characters, external inputs and Gram operators
are specialized in a separate estimate leaf. Constructive mathematics only.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSignPairCounts
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {I : Type*} [DecidableEq I]

/-- Natural cardinality of one sign pair inside a finite set. -/
def cellCount (s : Finset I) (a b : I → ℝ) (u v : ℝ) : ℕ :=
  ∑ x ∈ s, if a x = u ∧ b x = v then 1 else 0

/-- The four-cell character identity, without a finite-table premise. -/
theorem four_times_count (s : Finset I) (a b : I → ℝ)
    (ha : ∀ x ∈ s, a x = 1 ∨ a x = -1)
    (hb : ∀ x ∈ s, b x = 1 ∨ b x = -1)
    (u v : ℝ) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    4 * (cellCount s a b u v : ℝ) =
      (s.card : ℝ) + u * (∑ x ∈ s, a x) + v * (∑ x ∈ s, b x) +
        (u*v) * (∑ x ∈ s, a x * b x) := by
  calc
    _ = ∑ x ∈ s, (1 + u*a x + v*b x + (u*v)*(a x*b x)) := by
      simp only [cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rcases ha x hx with hax | hax <;>
        rcases hb x hx with hbx | hbx <;>
        rcases hu with hu | hu <;> rcases hv with hv | hv <;>
        norm_num [hax, hbx, hu, hv]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A quadratic weight is the sum of its four constant cell values. -/
theorem square_sum (s : Finset I) (a b : I → ℝ)
    (ha : ∀ x ∈ s, a x = 1 ∨ a x = -1)
    (hb : ∀ x ∈ s, b x = 1 ∨ b x = -1) (p q : ℝ) :
    (∑ x ∈ s, (p + q*(a x+b x))^2) =
      (p+2*q)^2 * (cellCount s a b 1 1 : ℝ) +
      p^2 * ((cellCount s a b 1 (-1) : ℝ) + (cellCount s a b (-1) 1 : ℝ)) +
      (p-2*q)^2 * (cellCount s a b (-1) (-1) : ℝ) := by
  calc
    _ = ∑ x ∈ s,
        ((p+2*q)^2 * (if a x = 1 ∧ b x = 1 then 1 else 0) +
        p^2 * ((if a x = 1 ∧ b x = -1 then 1 else 0) +
          (if a x = -1 ∧ b x = 1 then 1 else 0)) +
        (p-2*q)^2 * (if a x = -1 ∧ b x = -1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases ha x hx with hax | hax <;>
        rcases hb x hx with hbx | hbx <;> norm_num [hax, hbx] <;> ring
    _ = _ := by
      simp only [cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, mul_add, Finset.sum_add_distrib, Finset.mul_sum]

#print axioms four_times_count
#print axioms square_sum
end AES8.PaperSignPairCounts
