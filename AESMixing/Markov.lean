import AESMixing.Difference
import AESMixing.Centering

/-! Algebraic justification of composition after an independent common key. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

omit [AddCommGroup V] in
theorem sum_by_value (f : V → ℝ) (g : V → V) :
    (∑ x, f (g x)) = ∑ a, f a * ∑ x, if g x = a then (1 : ℝ) else 0 := by
  simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem difference_channel_average (s : Equiv.Perm V) (a : V) (f : V → ℝ) :
    (∑ x, f (difference s a x)) / Fintype.card V =
      ∑ d, f d * differenceChannel s d a := by
  rw [sum_by_value f (difference s a)]
  simp only [differenceChannel, Finset.sum_div, mul_div_assoc]

/-- The two keys in the finite sum are the shared input mask and the
independent key between the two permutation layers. -/
theorem independently_keyed_composition (s t : Equiv.Perm V) (a b : V) :
    ((∑ x, ∑ key,
      if t (s (x + a) + key) - t (s x + key) = b then (1 : ℝ) else 0) /
        Fintype.card V) / Fintype.card V =
      action (differenceChannel t) (fun d => differenceChannel s d a) b := by
  have hi (x key : V) : s x + key + difference s a x = s (x + a) + key := by
    simp [difference, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  have hkey (x : V) :
      (∑ key, if t (s (x + a) + key) - t (s x + key) = b then (1 : ℝ) else 0) /
        Fintype.card V = differenceChannel t b (difference s a x) := by
    simpa only [hi] using common_key_difference t (s x) (difference s a x) b
  rw [Finset.sum_div]
  simp_rw [hkey]
  exact difference_channel_average s a (fun d => differenceChannel t b d)

theorem differenceChannel_transpose (s : Equiv.Perm V) (a b : V) :
    differenceChannel s.symm a b = differenceChannel s b a := by
  have hi (x : V) : difference s.symm b (s x) = a ↔ difference s a x = b := by
    simp only [difference, Equiv.symm_apply_apply, sub_eq_iff_eq_add]
    constructor
    · intro h
      have hh := congrArg s h
      simpa only [Equiv.apply_symm_apply, add_comm] using hh.symm
    · intro h
      apply s.injective
      simpa only [Equiv.apply_symm_apply, add_comm] using h.symm
  unfold differenceChannel
  congr 1
  rw [← Equiv.sum_comp s (fun y => if difference s.symm b y = a then (1 : ℝ) else 0)]
  simp_rw [hi]

theorem differenceChannel_stationary (s : Equiv.Perm V) :
    action (differenceChannel s) (uniformExcept (0 : V)) = uniformExcept 0 := by
  funext b
  have hpoint (a : V) : differenceChannel s b a * uniformExcept 0 a =
      (differenceChannel s b a - if a = 0 then differenceChannel s b 0 else 0) /
        (Fintype.card V - 1 : ℝ) := by
    by_cases ha : a = 0
    · subst a; simp [uniformExcept]
    · simp [uniformExcept, ha, div_eq_mul_inv]
  unfold action
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, differenceChannel_row]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, differenceChannel_zero_column]
  by_cases hb : b = 0 <;> simp [uniformExcept, hb]

end AESMixing
