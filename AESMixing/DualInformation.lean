import AESMixing.AESPairing

/-! A bijective information set of a code gives the complementary information
set of its annihilator. Applied to every information set, this proves dual MDS. -/
noncomputable section
namespace AESMixing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Fintype V]

def subgroupRestriction (C : AddSubgroup (I → V)) (p : I → Prop)
    (c : C) : {i : I // p i} → V := fun i => c.val i.val

omit [Fintype V] in
theorem dual_supported_zero (B : CharacterPairing V) (C : AddSubgroup (I → V))
    (p : I → Prop) (hs : Function.Surjective (subgroupRestriction C p))
    (w : (B.product I).annihilator C) (hw : ∀ i, ¬ p i → w.val i = 0) :
    w.val = 0 := by
  classical
  funext i
  by_cases hi : p i
  · by_contra hwi
    obtain ⟨v,hv⟩ := B.nondegenerate (w.val i) hwi
    obtain ⟨c,hc⟩ := hs (fun j => if j.val = i then v else 0)
    have hpair := w.property c
    change (∏ j, B.value (w.val j) (c.val j)) = 1 at hpair
    have he : (∏ j, B.value (w.val j) (c.val j)) = B.value (w.val i) v := by
      rw [Finset.prod_eq_single i]
      · have hci := congrFun hc (⟨i,hi⟩ : {i // p i})
        change c.val i = if i = i then v else 0 at hci
        rw [if_pos rfl] at hci
        rw [hci]
      · intro j _ hji
        by_cases hj : p j
        · have hcj := congrFun hc (⟨j,hj⟩ : {i // p i})
          change c.val j = if j = i then v else 0 at hcj
          rw [if_neg hji] at hcj
          rw [hcj, B.zero_right]
        · rw [hw j hj, B.zero_left]
      · simp
    exact hv (he.symm.trans hpair)
  · exact hw i hi

omit [Fintype V] in
theorem dual_restriction_injective (B : CharacterPairing V) (C : AddSubgroup (I → V))
    (p : I → Prop) (hs : Function.Surjective (subgroupRestriction C p)) :
    Function.Injective (subgroupRestriction ((B.product I).annihilator C) (fun i => ¬ p i)) := by
  intro x y he
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply dual_supported_zero B C p hs (x-y)
  intro i hi
  have hh := congrFun he (⟨i,hi⟩ : {i // ¬ p i})
  change x.val i = y.val i at hh
  change x.val i - y.val i = 0
  exact sub_eq_zero.mpr hh

theorem dual_restriction_bijective (B : CharacterPairing V) (C : AddSubgroup (I → V))
    [Fintype C] (p : I → Prop) (hs : Function.Bijective (subgroupRestriction C p)) :
    Function.Bijective (subgroupRestriction ((B.product I).annihilator C) (fun i => ¬ p i)) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨dual_restriction_injective B C p hs.surjective, ?_⟩
  have hc : Fintype.card C = Fintype.card ({i // p i} → V) :=
    Fintype.card_congr (Equiv.ofBijective (subgroupRestriction C p) hs)
  have hall := (B.product I).annihilator_card C
  have hsplit : Fintype.card (I → V) =
      Fintype.card ({i // p i} → V) * Fintype.card ({i // ¬ p i} → V) := by
    rw [Fintype.card_congr (Equiv.piEquivPiSubtypeProd p (fun _ => V)), Fintype.card_prod]
  rw [hsplit, ← hc] at hall
  apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos (α := C))
  simpa only [Nat.mul_comm] using hall

end AESMixing
