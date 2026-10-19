import AESMixing.CodeResponse
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Character sums and annihilator cardinality for finite additive codes.
This is the algebraic part of the high-dimensional code-duality argument. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable

theorem additive_character_sum {X : Type*} [AddCommGroup X] [Fintype X]
    (χ : X → ℝ) (hadd : ∀ x y, χ (x+y) = χ x * χ y) :
    (∑ x, χ x) = if ∀ x, χ x = 1 then (Fintype.card X : ℝ) else 0 := by
  classical
  by_cases h : ∀ x, χ x = 1
  · simp [h]
  · rw [if_neg h]
    obtain ⟨w,hw⟩ := not_forall.mp h
    have he := Equiv.sum_comp (Equiv.addLeft w) χ
    change (∑ x, χ (w+x)) = ∑ x, χ x at he
    simp_rw [hadd, ← Finset.mul_sum] at he
    have hz : (χ w - 1) * (∑ x, χ x) = 0 := by nlinarith [he]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hw)

structure CharacterPairing (X : Type*) [AddCommGroup X] where
  value : X → X → ℝ
  zero_right : ∀ x, value x 0 = 1
  add_right : ∀ x y z, value x (y+z) = value x y * value x z
  symmetric : ∀ x y, value x y = value y x
  nondegenerate : ∀ x, x ≠ 0 → ∃ y, value x y ≠ 1

variable {X : Type*} [AddCommGroup X]

theorem CharacterPairing.zero_left (B : CharacterPairing X) (x : X) : B.value 0 x = 1 := by
  rw [B.symmetric, B.zero_right]

theorem CharacterPairing.add_left (B : CharacterPairing X) (x y z : X) :
    B.value (x+y) z = B.value x z * B.value y z := by
  rw [B.symmetric, B.add_right, B.symmetric z x, B.symmetric z y]

def CharacterPairing.annihilator (B : CharacterPairing X) (C : AddSubgroup X) : AddSubgroup X where
  carrier := {w | ∀ c : C, B.value w c.val = 1}
  zero_mem' := by intro c; exact B.zero_left c.val
  add_mem' := by
    intro x y hx hy c
    rw [B.add_left, hx c, hy c, one_mul]
  neg_mem' := by
    intro x hx c
    have h := B.add_left (-x) x c.val
    rw [neg_add_cancel, B.zero_left, hx c, mul_one] at h
    exact h.symm

noncomputable instance [Fintype X] (B : CharacterPairing X) (C : AddSubgroup X) :
    Fintype (B.annihilator C) := Fintype.ofFinite _

theorem CharacterPairing.full_sum [Fintype X] (B : CharacterPairing X) (x : X) :
    (∑ w, B.value w x) = if x = 0 then (Fintype.card X : ℝ) else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, B.zero_right]
  · rw [if_neg hx, additive_character_sum (fun w => B.value w x) (fun y z => B.add_left y z x)]
    apply if_neg
    intro h
    obtain ⟨w,hw⟩ := B.nondegenerate x hx
    exact hw ((B.symmetric x w).trans (h w))

theorem CharacterPairing.subgroup_sum (B : CharacterPairing X)
    (C : AddSubgroup X) [Fintype C] (w : X) :
    (∑ c : C, B.value w c.val) =
      if w ∈ B.annihilator C then (Fintype.card C : ℝ) else 0 := by
  classical
  have he := additive_character_sum (fun c : C => B.value w c.val)
    (fun c d => B.add_right w c.val d.val)
  by_cases hw : w ∈ B.annihilator C
  · have hh : ∀ c : C, B.value w c.val = 1 := hw
    rw [if_pos hw]
    simpa only [if_pos hh] using he
  · have hh : ¬ ∀ c : C, B.value w c.val = 1 := hw
    rw [if_neg hw]
    simpa only [if_neg hh] using he

theorem real_indicator_card {A : Type*} [Fintype A] (p : A → Prop) [Fintype {a // p a}] :
    (∑ a, if p a then (1 : ℝ) else 0) = Fintype.card {a // p a} := by
  classical
  rw [Fintype.card_subtype p]
  simp

theorem CharacterPairing.annihilator_card [Fintype X]
    (B : CharacterPairing X) (C : AddSubgroup X) [Fintype C] :
    Fintype.card (B.annihilator C) * Fintype.card C = Fintype.card X := by
  classical
  have htotal : (∑ w : X, ∑ c : C, B.value w c.val) = (Fintype.card X : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [B.full_sum]
    have he (c : C) : c.val = 0 ↔ c = 0 := by
      constructor
      · intro h
        exact Subtype.ext h
      · rintro rfl; rfl
    simp only [he]
    simp
  simp_rw [B.subgroup_sum] at htotal
  have ht : (∑ w : X, if w ∈ B.annihilator C then (Fintype.card C : ℝ) else 0) =
      (Fintype.card (B.annihilator C) : ℝ) * Fintype.card C := by
    have hi := real_indicator_card (fun w : X => w ∈ B.annihilator C)
    calc
      _ = (∑ w : X, if w ∈ B.annihilator C then (1 : ℝ) else 0) * Fintype.card C := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        split_ifs <;> simp
      _ = _ := by rw [hi]
  rw [ht] at htotal
  exact_mod_cast htotal

end AESMixing
