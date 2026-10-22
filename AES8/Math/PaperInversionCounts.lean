import AES8.Math.PaperArtinSchreier
import AESMixing.InversionDDT

/-! Literal difference counts for inversion on arbitrary finite binary fields.
The exceptional inputs zero and one are counted separately from the
Artin--Schreier fiber; no table certificate or fixed field size is used. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionCounts
open AESMixing PaperFieldTrace
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

theorem difference_one (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    difference invPermutation 1 t = (t^2+t)⁻¹ := by
  have ht : t+1 ≠ 0 := by
    intro h
    exact ht1 (CharTwo.add_eq_zero.mp h)
  change (t+1)⁻¹-t⁻¹ = _
  rw [CharTwo.sub_eq_add, inv_add_inv ht ht0]
  have hn : t+1+t = (1 : F) := by
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [hn, one_div]
  congr 1
  ring

theorem indicator (c t : F) (hc : c ≠ 0) :
    (if difference invPermutation 1 t=c then (1 : ℕ) else 0) =
      (if t^2+t=c⁻¹ then 1 else 0) +
      (if c=1 then (if t=0 ∨ t=1 then 1 else 0) else 0) := by
  by_cases ht0 : t=0
  · subst t
    simp [difference, invPermutation, inv_ne_zero hc, eq_comm]
  by_cases ht1 : t=1
  · subst t
    simp [difference, invPermutation, CharTwo.add_self_eq_zero, CharTwo.neg_eq,
      inv_ne_zero hc, eq_comm]
  rw [difference_one t ht0 ht1]
  have hi : (t^2+t)⁻¹=c ↔ t^2+t=c⁻¹ := by
    constructor <;> intro h
    · simpa using congrArg Inv.inv h
    · rw [h, inv_inv]
  simp [hi, ht0, ht1]

theorem count_one (c : F) (hc : c ≠ 0) :
    (Finset.univ.filter (fun t : F => difference invPermutation 1 t=c)).card =
      (if trace c⁻¹=0 then 2 else 0) + (if c=1 then 2 else 0) := by
  rw [Finset.card_filter]
  simp_rw [indicator c _ hc]
  rw [Finset.sum_add_distrib]
  have ha : (∑ t : F, if t^2+t=c⁻¹ then (1 : ℕ) else 0) =
      if trace c⁻¹=0 then 2 else 0 := by
    rw [← Finset.card_filter]
    exact PaperArtinSchreier.fiber_card c⁻¹
  rw [ha]
  congr 1
  by_cases hc1 : c=1
  · simp only [hc1, if_true]
    have hset : Finset.univ.filter (fun t : F => t=0 ∨ t=1) = {0,1} := by
      ext t
      simp
    rw [← Finset.card_filter, hset]
    simp [zero_ne_one]
  · simp [hc1]

theorem channel_one (c : F) (hc : c ≠ 0) :
    differenceChannel invPermutation c 1 =
      (2*((if trace c⁻¹=0 then (1 : ℝ) else 0)+
          (if c=1 then 1 else 0)))/(Fintype.card F : ℝ) := by
  unfold differenceChannel
  rw [Finset.sum_boole, count_one c hc]
  congr 1
  split_ifs <;> norm_num

theorem channel (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    differenceChannel invPermutation b a =
      (2*((if trace (a*b)⁻¹=0 then (1 : ℝ) else 0)+
          (if a*b=1 then 1 else 0)))/(Fintype.card F : ℝ) := by
  rw [inversion_channel_scale a b ha]
  exact channel_one (a*b) (mul_ne_zero ha hb)

end AES8.PaperInversionCounts
