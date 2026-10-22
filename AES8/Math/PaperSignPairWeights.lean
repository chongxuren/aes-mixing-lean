import AES8.Math.PaperSignPairCounts

/-!
# Weights on the four sign cells

This generic finite-set algebra supplies the paper's absolute cubic count.
It assigns arbitrary real weights to the same four sign pairs as the existing
symbolic histogram. It enumerates no byte field or trace values.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSignPairWeights
open AES8.PaperSignPairCounts
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {I : Type*} [DecidableEq I]

/-- An arbitrary weight is constant on each of the four sign cells. -/
theorem weighted_sum (s : Finset I) (a b : I → ℝ)
    (ha : ∀ x ∈ s, a x = 1 ∨ a x = -1)
    (hb : ∀ x ∈ s, b x = 1 ∨ b x = -1) (w : ℝ → ℝ → ℝ) :
    (∑ x ∈ s, w (a x) (b x)) =
      w 1 1 * (cellCount s a b 1 1 : ℝ) +
      w 1 (-1) * (cellCount s a b 1 (-1) : ℝ) +
      w (-1) 1 * (cellCount s a b (-1) 1 : ℝ) +
      w (-1) (-1) * (cellCount s a b (-1) (-1) : ℝ) := by
  calc
    _ = ∑ x ∈ s,
        (w 1 1 * (if a x = 1 ∧ b x = 1 then 1 else 0) +
        w 1 (-1) * (if a x = 1 ∧ b x = -1 then 1 else 0) +
        w (-1) 1 * (if a x = -1 ∧ b x = 1 then 1 else 0) +
        w (-1) (-1) * (if a x = -1 ∧ b x = -1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases ha x hx with hax | hax <;>
        rcases hb x hx with hbx | hbx <;> norm_num [hax, hbx]
    _ = _ := by
      simp only [cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, Finset.sum_add_distrib, Finset.mul_sum]

#print axioms weighted_sum
end AES8.PaperSignPairWeights
