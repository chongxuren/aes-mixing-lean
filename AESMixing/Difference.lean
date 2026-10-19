import AESMixing.Whitening
import Mathlib.Algebra.Group.Units.Equiv

/-! Difference channels of actual permutations of finite additive groups.
All probabilities below are explicit finite sums over a uniform retained key. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def difference (s : Equiv.Perm V) (a x : V) : V := s (x + a) - s x

def differenceChannel (s : Equiv.Perm V) (b a : V) : ℝ :=
  (∑ x, if difference s a x = b then (1 : ℝ) else 0) / Fintype.card V

omit [Fintype V] [DecidableEq V] in
theorem difference_zero_iff (s : Equiv.Perm V) (a x : V) :
    difference s a x = 0 ↔ a = 0 := by
  simp [difference, sub_eq_zero, s.injective.eq_iff]

theorem differenceChannel_nonneg (s : Equiv.Perm V) (b a : V) :
    0 ≤ differenceChannel s b a := by
  unfold differenceChannel
  positivity

theorem differenceChannel_column (s : Equiv.Perm V) (a : V) :
    (∑ b, differenceChannel s b a) = 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold differenceChannel
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [hn]

theorem differenceChannel_row (s : Equiv.Perm V) (b : V) :
    (∑ a, differenceChannel s b a) = 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hx (x : V) : (∑ a, if difference s a x = b then (1 : ℝ) else 0) = 1 := by
    let e := ((Equiv.addLeft x).trans s).trans (Equiv.subRight (s x))
    have h := Equiv.sum_comp e (fun z => if z = b then (1 : ℝ) else 0)
    change (∑ a, if difference s a x = b then (1 : ℝ) else 0) =
      ∑ z, if z = b then (1 : ℝ) else 0 at h
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  unfold differenceChannel
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hx]
  simp [hn]

theorem differenceChannel_zero_row (s : Equiv.Perm V) (a : V) :
    differenceChannel s 0 a = if a = 0 then 1 else 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [differenceChannel, difference_zero_iff]
  by_cases ha : a = 0 <;> simp [ha, hn]

theorem differenceChannel_zero_column (s : Equiv.Perm V) (b : V) :
    differenceChannel s b 0 = if b = 0 then 1 else 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hb : b = 0
  · simp [differenceChannel, difference, hb, hn]
  · simp [differenceChannel, difference, hb, Ne.symm hb]

/-- A uniform common key makes the next difference law depend only on the
input difference, even when the unkeyed first state is arbitrary. -/
theorem common_key_difference (s : Equiv.Perm V) (x a b : V) :
    (∑ key, if s (x + key + a) - s (x + key) = b then (1 : ℝ) else 0) /
      Fintype.card V = differenceChannel s b a := by
  unfold differenceChannel
  congr 1
  exact Equiv.sum_comp (Equiv.addLeft x)
    (fun z => if difference s a z = b then (1 : ℝ) else 0)

/-- Output whitening makes the first output uniform independently of the
difference. This identity is pointwise in the two pre-whitening states. -/
theorem output_key_pair (u v y b : V) :
    (∑ key, if u + key = y ∧ v + key = y + b then (1 : ℝ) else 0) /
      Fintype.card V =
        (if v - u = b then (1 : ℝ) else 0) / Fintype.card V := by
  have hcond (key : V) : (u + key = y ∧ v + key = y + b) ↔
      (key = y - u ∧ v - u = b) := by
    constructor
    · rintro ⟨h1, h2⟩
      have hk : key = y - u := by exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h1)
      refine ⟨hk, ?_⟩
      rw [hk] at h2
      apply add_left_cancel (a := y)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2
    · rintro ⟨rfl, hb⟩
      constructor
      · simp [add_comm u]
      · rw [← hb]
        simp [sub_eq_add_neg, add_left_comm]
  simp_rw [hcond]
  by_cases hb : v - u = b <;> simp [hb]

end AESMixing
