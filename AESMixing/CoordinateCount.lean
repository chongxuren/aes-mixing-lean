import AESMixing.MDSInterpolation
import Mathlib.Data.Fintype.BigOperators

/-! Exact finite counts for coordinate restrictions. These are the
counting rules used after an MDS information-set bijection is established. -/
namespace AESMixing
open scoped BigOperators

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [Zero V] [DecidableEq V]

def zeroRestrictedEquiv (p : I → Prop) [DecidablePred p] :
    {f : I → V // ∀ i, p i → f i = 0} ≃ ({i : I // ¬ p i} → V) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : p i then 0 else f ⟨i,h⟩, by
    intro i hi
    simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : p i
    · simp [hi, f.property i hi]
    · simp [hi]
  right_inv f := by
    funext i
    simp [i.property]

theorem zero_restricted_card (p : I → Prop) [DecidablePred p] :
    Fintype.card {f : I → V // ∀ i, p i → f i = 0} =
      Fintype.card V ^ Fintype.card {i : I // ¬ p i} := by
  rw [Fintype.card_congr (zeroRestrictedEquiv p), Fintype.card_fun]

def prescribedEquiv (p : I → Prop) [DecidablePred p] (target : I → V) :
    {f : I → V // ∀ i, p i → f i = target i} ≃ ({i : I // ¬ p i} → V) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : p i then target i else f ⟨i,h⟩, by
    intro i hi
    simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : p i
    · simp [hi, f.property i hi]
    · simp [hi]
  right_inv f := by
    funext i
    simp [i.property]

omit [Zero V] in
theorem prescribed_card (p : I → Prop) [DecidablePred p] (target : I → V) :
    Fintype.card {f : I → V // ∀ i, p i → f i = target i} =
      Fintype.card V ^ Fintype.card {i : I // ¬ p i} := by
  rw [Fintype.card_congr (prescribedEquiv p target), Fintype.card_fun]

def pullbackConstraintEquiv {A B : Type*} (e : A ≃ B) (p : B → Prop) :
    {a : A // p (e a)} ≃ {b : B // p b} where
  toFun a := ⟨e a.val, a.property⟩
  invFun b := ⟨e.symm b.val, by simpa only [e.apply_symm_apply] using b.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)

omit [Zero V] in
theorem bijective_prescribed_card {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ≃ (I → V)) (p : I → Prop) [DecidablePred p] (target : I → V) :
    Fintype.card {a : A // ∀ i, p i → e a i = target i} =
      Fintype.card V ^ Fintype.card {i : I // ¬ p i} := by
  rw [Fintype.card_congr (pullbackConstraintEquiv e (fun f => ∀ i, p i → f i = target i))]
  exact prescribed_card p target

end AESMixing
