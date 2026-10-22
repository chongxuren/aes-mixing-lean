import AESConcrete.ActivityCodeMoment
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual shortening and puncturing of activity codes

`zeroSubgroup` imposes actual zero coordinates before `minorCode` restricts
to the retained physical coordinate subtype. Information sets are proved
from a disjoint original information set, never assumed for the minor.
The general predicates allow several zero and punctured coordinates.

Constructive mathematics only; no attacks. Independent uniform retained
keys, whitening, omitted final MixColumns, ordered-distinct pairs and
10/14/16 stay fixed. This module supplies geometry, not a physical cap.
-/

noncomputable section
namespace AESConcrete.ActivityMinorGeometry
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ActivityCodeGeometry (wordCode)
open AESConcrete.ActivityCodeMoment (wordCode_predicate_restriction_bijective)
open AESConcrete.ActualMarkedCodeDual (selectionRange selectionEquiv selection_complement_card)
attribute [local instance] Classical.propDecidable

section Geometry
variable {J V A : Type*} [AddCommGroup V]

/-- Impose zero on the original physical coordinates in `Z`. -/
def zeroSubgroup (C : AddSubgroup (J → V)) (Z : J → Prop) :
    AddSubgroup (J → V) where
  carrier := {x | x ∈ C ∧ ∀ j, Z j → x j = 0}
  zero_mem' := ⟨C.zero_mem, by intros; rfl⟩
  add_mem' := by
    rintro x y ⟨hx, hxZ⟩ ⟨hy, hyZ⟩
    refine ⟨C.add_mem hx hy, ?_⟩
    intro j hj
    simp only [Pi.add_apply, hxZ j hj, hyZ j hj, zero_add]
  neg_mem' := by
    rintro x ⟨hx, hxZ⟩
    refine ⟨C.neg_mem hx, ?_⟩
    intro j hj
    simp only [Pi.neg_apply, hxZ j hj, neg_zero]

@[simp]
theorem mem_zeroSubgroup_iff (C : AddSubgroup (J → V))
    (Z : J → Prop) (x : J → V) :
    x ∈ zeroSubgroup C Z ↔ x ∈ C ∧ ∀ j, Z j → x j = 0 := Iff.rfl

/-- Restriction preserves the original labels and their physical ordering. -/
def restrictHom (L : J → Prop) : (J → V) →+ ({j : J // L j} → V) where
  toFun x j := x j.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- First shorten on `Z`, then puncture every coordinate outside `L`. -/
def minorCode (C : AddSubgroup (J → V)) (Z L : J → Prop) :
    AddSubgroup ({j : J // L j} → V) :=
  (zeroSubgroup C Z).map (restrictHom L)

theorem mem_minorCode_iff (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (y : {j : J // L j} → V) :
    y ∈ minorCode C Z L ↔ ∃ x : J → V,
      x ∈ C ∧ (∀ j, Z j → x j = 0) ∧ restrictHom L x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp hy
    exact ⟨x, hx.1, hx.2, hxy⟩
  · rintro ⟨x, hx, hxZ, hxy⟩
    exact AddSubgroup.mem_map.mpr ⟨x, ⟨hx, hxZ⟩, hxy⟩

/-- The source enumeration maps each shortened word to its actual minor. -/
def minorMap (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (c : zeroSubgroup C Z) : minorCode C Z L :=
  ⟨restrictHom L c.val, AddSubgroup.mem_map.mpr ⟨c.val, c.property, rfl⟩⟩

@[simp]
theorem minorMap_val (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (c : zeroSubgroup C Z) : (minorMap C Z L c).val = restrictHom L c.val := rfl

theorem minorMap_surjective (C : AddSubgroup (J → V)) (Z L : J → Prop) :
    Function.Surjective (minorMap C Z L) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- This equivalence requires an injective actual restriction; cardinality
alone is not used to infer absence of puncturing multiplicity. -/
def minorSourceEquiv (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (hinj : Function.Injective
      (fun c : zeroSubgroup C Z => restrictHom L c.val)) :
    zeroSubgroup C Z ≃ minorCode C Z L :=
  Equiv.ofBijective (minorMap C Z L)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), minorMap_surjective C Z L⟩

@[simp]
theorem minorSourceEquiv_val (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (hinj : Function.Injective
      (fun c : zeroSubgroup C Z => restrictHom L c.val))
    (c : zeroSubgroup C Z) :
    (minorSourceEquiv C Z L hinj c).val = restrictHom L c.val := rfl

/-- Zero-coordinate labels precede the selected retained labels. This is
only an information-set labeling; retained tensor legs keep subtype order. -/
def zeroSelected (Z : J → Prop) (p : A → J) : ({j : J // Z j} ⊕ A) → J :=
  Sum.elim Subtype.val p

/-- Fixing the zero part of an original information set leaves a genuine
bijection from shortened words to the selected remaining values. -/
theorem zeroSubgroup_projection_bijective (C : AddSubgroup (J → V))
    (Z : J → Prop) (p : A → J)
    (hc : Function.Bijective (fun c : C =>
      fun k : {j : J // Z j} ⊕ A => c.val (zeroSelected Z p k))) :
    Function.Bijective (fun c : zeroSubgroup C Z => fun a : A => c.val (p a)) := by
  constructor
  · intro x y hxy
    have he : (⟨x.val, x.property.1⟩ : C) = ⟨y.val, y.property.1⟩ := by
      apply hc.1
      funext k
      rcases k with j | a
      · exact (x.property.2 j.val j.property).trans
          (y.property.2 j.val j.property).symm
      · exact congrFun hxy a
    apply Subtype.ext
    exact congrArg (fun c : C => c.val) he
  · intro w
    obtain ⟨x, hx⟩ := hc.2 (Sum.elim (fun _ => 0) w)
    have hxZ : ∀ j, Z j → x.val j = 0 := by
      intro j hj
      exact congrFun hx (Sum.inl ⟨j, hj⟩)
    refine ⟨⟨x.val, x.property, hxZ⟩, ?_⟩
    funext a
    exact congrFun hx (Sum.inr a)

theorem minor_restriction_injective (C : AddSubgroup (J → V))
    (Z L : J → Prop) (p : A → {j : J // L j})
    (hc : Function.Bijective (fun c : C => fun k : {j : J // Z j} ⊕ A =>
      c.val (zeroSelected Z (fun a => (p a).val) k))) :
    Function.Injective (fun c : zeroSubgroup C Z => restrictHom L c.val) := by
  intro x y hxy
  apply (zeroSubgroup_projection_bijective C Z (fun a => (p a).val) hc).1
  funext a
  exact congrFun hxy (p a)

/-- A minor inherits a selected information set from the actual original
information set consisting of the zero coordinates and these selected legs. -/
theorem minor_projection_bijective (C : AddSubgroup (J → V))
    (Z L : J → Prop) (p : A → {j : J // L j})
    (hc : Function.Bijective (fun c : C => fun k : {j : J // Z j} ⊕ A =>
      c.val (zeroSelected Z (fun a => (p a).val) k))) :
    Function.Bijective (fun c : minorCode C Z L => fun a : A => c.val (p a)) := by
  let e := minorSourceEquiv C Z L (minor_restriction_injective C Z L p hc)
  have hz := zeroSubgroup_projection_bijective C Z (fun a => (p a).val) hc
  have h := hz.comp e.symm.bijective
  have he : (fun c : minorCode C Z L =>
      fun a : A => (e.symm c).val (p a).val) =
      (fun c : minorCode C Z L => fun a : A => c.val (p a)) := by
    funext c a
    have hh := congrArg (fun d : minorCode C Z L => d.val (p a)) (e.apply_symm_apply c)
    exact hh
  change Function.Bijective (fun c : minorCode C Z L =>
    fun a : A => (e.symm c).val (p a).val) at h
  rw [he] at h
  exact h

end Geometry

section InformationSets
variable {J V A : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [Fintype A]

instance zeroSubgroupFintype (C : AddSubgroup (J → V)) (Z : J → Prop) :
    Fintype (zeroSubgroup C Z) := Fintype.ofFinite _

instance minorCodeFintype (C : AddSubgroup (J → V)) (Z L : J → Prop) :
    Fintype (minorCode C Z L) := Fintype.ofFinite _

/-- All restrictions of size `t` are actual information sets. -/
def HasInformationSets (C : AddSubgroup (J → V)) (t : ℕ) : Prop :=
  ∀ P : J → Prop, Fintype.card {j : J // P j} = t →
    Function.Bijective (subgroupRestriction C P)

omit [DecidableEq J] [Fintype V] in
theorem information_sets_zero_mem (C : AddSubgroup (J → V))
    (hC : HasInformationSets C 0) (x : J → V) : x ∈ C ↔ x = 0 := by
  have hc := hC (fun _ => False) (by simp)
  constructor
  · intro hx
    have he : (⟨x, hx⟩ : C) = 0 := by
      apply hc.1
      funext j
      exact j.property.elim
    exact congrArg Subtype.val he
  · rintro rfl
    exact C.zero_mem

omit [DecidableEq J] [Fintype V] in
theorem information_sets_full_mem (C : AddSubgroup (J → V))
    (hC : HasInformationSets C (Fintype.card J)) (x : J → V) : x ∈ C := by
  have hc := hC (fun _ => True) (by simp)
  obtain ⟨c, hc⟩ := hc.2 (fun j => x j.val)
  have he : c.val = x := by
    funext j
    exact congrFun hc (⟨j, trivial⟩ : {j : J // True})
  exact he ▸ c.property

omit [DecidableEq J] [Fintype V] in
theorem projection_bijective_of_information_sets (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (p : A → J)
    (hp : Function.Injective p) (hsize : Fintype.card A = t) :
    Function.Bijective (fun c : C => fun a : A => c.val (p a)) := by
  let e := selectionEquiv p hp
  have hc := hC (selectionRange p) ((Fintype.card_congr e).symm.trans hsize)
  have hr : Function.Bijective
      (fun g : {j : J // selectionRange p j} → V => fun a : A => g (e a)) :=
    (Equiv.arrowCongr e.symm (Equiv.refl V)).bijective
  have h := hr.comp hc
  change Function.Bijective (fun c : C => fun a : A => c.val (p a)) at h
  exact h

omit [Fintype V] in
/-- Any smaller actual coordinate restriction is surjective: extend its
distinct labels to a size-`t` information set and fix the new labels to zero. -/
theorem projection_surjective_of_information_sets_le (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (hJ : t ≤ Fintype.card J)
    (p : A → J) (hp : Function.Injective p) (hsize : Fintype.card A ≤ t) :
    Function.Surjective (fun c : C => fun a : A => c.val (p a)) := by
  have hcompl := selection_complement_card p hp
  obtain ⟨q⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (t - Fintype.card A)) (β := {j : J // ¬ selectionRange p j})
    (by rw [Fintype.card_fin, hcompl]; omega)
  let r : A ⊕ Fin (t - Fintype.card A) → J := Sum.elim p (fun b => (q b).val)
  have hr : Function.Injective r := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (hp hxy)
    · exact ((q y).property ⟨x, hxy⟩).elim
    · exact ((q x).property ⟨y, hxy.symm⟩).elim
    · exact congrArg Sum.inr (q.injective (Subtype.ext hxy))
  have hc := projection_bijective_of_information_sets C t hC r hr
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  intro w
  obtain ⟨c, hc⟩ := hc.2 (Sum.elim w (fun _ => 0))
  refine ⟨c, ?_⟩
  funext a
  exact congrFun hc (Sum.inl a)

omit [DecidableEq J] [Fintype V] in
/-- Fixing at least the count dimension's worth of distinct original
coordinates to zero leaves only the zero point. -/
theorem zeroSubgroup_mem_iff_eq_zero_of_le (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z : J → Prop)
    (hZ : t ≤ Fintype.card {j : J // Z j}) (x : J → V) :
    x ∈ zeroSubgroup C Z ↔ x = 0 := by
  obtain ⟨p⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin t) (β := {j : J // Z j}) (by simpa only [Fintype.card_fin] using hZ)
  have hc := projection_bijective_of_information_sets C t hC
    (fun a => (p a).val) (Subtype.val_injective.comp p.injective)
    (by simp only [Fintype.card_fin])
  constructor
  · intro hx
    have he : (⟨x, hx.1⟩ : C) = 0 := by
      apply hc.1
      funext a
      exact hx.2 (p a).val (p a).property
    exact congrArg Subtype.val he
  · rintro rfl
    exact (zeroSubgroup C Z).zero_mem

omit [Fintype J] [DecidableEq J] [Fintype A] in
theorem zeroSelected_injective (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (p : A → {j : J // L j})
    (hp : Function.Injective p) :
    Function.Injective (zeroSelected Z (fun a => (p a).val)) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Subtype.ext hxy)
  · change x.val = (p y).val at hxy
    have hy : L x.val := by rw [hxy]; exact (p y).property
    exact (hZL x.val x.property hy).elim
  · change (p x).val = y.val at hxy
    have hx : L y.val := by rw [← hxy]; exact (p x).property
    exact (hZL y.val y.property hx).elim
  · exact congrArg Sum.inr (hp (Subtype.ext hxy))

omit [Fintype V] in
/-- When the remaining source dimension is at least the retained length,
restriction is surjective, including genuinely noninjective puncturing. -/
theorem minor_source_surjective_of_information_sets_le (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (hJ : t ≤ Fintype.card J)
    (Z L : J → Prop) (hZL : ∀ j, Z j → ¬ L j)
    (hdim : Fintype.card {j : J // Z j} + Fintype.card {j : J // L j} ≤ t) :
    Function.Surjective (fun c : zeroSubgroup C Z => restrictHom L c.val) := by
  have hc := projection_surjective_of_information_sets_le C t hC hJ
    (zeroSelected Z (fun j : {j : J // L j} => j.val))
    (zeroSelected_injective Z L hZL (fun j => j) (fun _ _ h => h))
    (by simpa only [Fintype.card_sum] using hdim)
  intro w
  obtain ⟨c, hc⟩ := hc (Sum.elim (fun _ => 0) w)
  have hcZ : ∀ j, Z j → c.val j = 0 := by
    intro j hj
    exact congrFun hc (Sum.inl ⟨j, hj⟩)
  refine ⟨⟨c.val, c.property, hcZ⟩, ?_⟩
  funext j
  exact congrFun hc (Sum.inr j)

omit [DecidableEq J] [Fintype V] in
theorem minor_original_projection_bijective (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (p : A → {j : J // L j})
    (hp : Function.Injective p)
    (hdim : Fintype.card {j : J // Z j} + Fintype.card A = t) :
    Function.Bijective (fun c : C => fun k : {j : J // Z j} ⊕ A =>
      c.val (zeroSelected Z (fun a => (p a).val) k)) := by
  apply projection_bijective_of_information_sets C t hC
    (zeroSelected Z (fun a => (p a).val)) (zeroSelected_injective Z L hZL p hp)
  simpa only [Fintype.card_sum] using hdim

omit [DecidableEq J] [Fintype V] in
theorem minor_projection_bijective_of_information_sets (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (p : A → {j : J // L j})
    (hp : Function.Injective p)
    (hdim : Fintype.card {j : J // Z j} + Fintype.card A = t) :
    Function.Bijective (fun c : minorCode C Z L => fun a : A => c.val (p a)) :=
  minor_projection_bijective C Z L p
    (minor_original_projection_bijective C t hC Z L hZL p hp hdim)

omit [DecidableEq J] [Fintype V] in
/-- Every retained predicate of the remaining count dimension is an actual
minor information set. This is the predicate interface for moment bounds. -/
theorem minor_information_sets (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : J // Z j} ≤ t) :
    HasInformationSets (minorCode C Z L) (t - Fintype.card {j : J // Z j}) := by
  intro P hP
  have h := minor_projection_bijective_of_information_sets C t hC Z L hZL
    (fun j : {j : {j : J // L j} // P j} => j.val) Subtype.val_injective
    (by rw [hP]; omega)
  change Function.Bijective (subgroupRestriction (minorCode C Z L) P) at h
  exact h

omit [DecidableEq J] in
theorem minor_card_of_projection (C : AddSubgroup (J → V)) (Z L : J → Prop)
    (p : A → {j : J // L j})
    (hc : Function.Bijective (fun c : minorCode C Z L => fun a : A => c.val (p a))) :
    Fintype.card (minorCode C Z L) = Fintype.card V ^ Fintype.card A := by
  rw [Fintype.card_congr (Equiv.ofBijective _ hc), Fintype.card_fun]

omit [DecidableEq J] [Fintype V] in
/-- Enough retained coordinates provide an information set after shortening.
No particular choice of those coordinates is part of the minor definition. -/
theorem minor_source_injective_of_information_sets (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : J // Z j} ≤ t)
    (hL : t - Fintype.card {j : J // Z j} ≤ Fintype.card {j : J // L j}) :
    Function.Injective (fun c : zeroSubgroup C Z => restrictHom L c.val) := by
  obtain ⟨p⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (t - Fintype.card {j : J // Z j})) (β := {j : J // L j})
    (by simpa only [Fintype.card_fin] using hL)
  apply minor_restriction_injective C Z L p
  apply minor_original_projection_bijective C t hC Z L hZL p p.injective
  simp only [Fintype.card_fin]
  omega

omit [DecidableEq J] in
theorem minor_card_of_information_sets (C : AddSubgroup (J → V))
    (t : ℕ) (hC : HasInformationSets C t) (Z L : J → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : J // Z j} ≤ t)
    (hL : t - Fintype.card {j : J // Z j} ≤ Fintype.card {j : J // L j}) :
    Fintype.card (minorCode C Z L) =
      Fintype.card V ^ (t - Fintype.card {j : J // Z j}) := by
  obtain ⟨p⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (t - Fintype.card {j : J // Z j})) (β := {j : J // L j})
    (by simpa only [Fintype.card_fin] using hL)
  have hp := minor_projection_bijective_of_information_sets C t hC Z L hZL p
    p.injective (by simp only [Fintype.card_fin]; omega)
  simpa only [Fintype.card_fin] using minor_card_of_projection C Z L p hp

end InformationSets

section Word

theorem wordCode_information_sets (U : Fin 16) :
    HasInformationSets (wordCode U) (maskSize U) :=
  wordCode_predicate_restriction_bijective U

/-- Arbitrary zero and retained coordinate sets of the actual word image. -/
abbrev wordMinor (U : Fin 16) (Z L : Fin 4 → Prop) := minorCode (wordCode U) Z L

theorem wordMinor_projection_bijective {A : Type*} [Fintype A]
    (U : Fin 16) (Z L : Fin 4 → Prop) (hZL : ∀ j, Z j → ¬ L j)
    (p : A → {j : Fin 4 // L j}) (hp : Function.Injective p)
    (hdim : Fintype.card {j : Fin 4 // Z j} + Fintype.card A = maskSize U) :
    Function.Bijective (fun c : wordMinor U Z L => fun a : A => c.val (p a)) :=
  minor_projection_bijective_of_information_sets (wordCode U) (maskSize U)
    (wordCode_information_sets U) Z L hZL p hp hdim

theorem wordMinor_information_sets (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : Fin 4 // Z j} ≤ maskSize U) :
    HasInformationSets (wordMinor U Z L)
      (maskSize U - Fintype.card {j : Fin 4 // Z j}) :=
  minor_information_sets (wordCode U) (maskSize U) (wordCode_information_sets U)
    Z L hZL hZ

theorem wordMinor_source_injective (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : Fin 4 // Z j} ≤ maskSize U)
    (hL : maskSize U - Fintype.card {j : Fin 4 // Z j} ≤
      Fintype.card {j : Fin 4 // L j}) :
    Function.Injective (fun c : zeroSubgroup (wordCode U) Z => restrictHom L c.val) :=
  minor_source_injective_of_information_sets (wordCode U) (maskSize U)
    (wordCode_information_sets U) Z L hZL hZ hL

theorem wordMinor_source_surjective (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j)
    (hdim : Fintype.card {j : Fin 4 // Z j} + Fintype.card {j : Fin 4 // L j} ≤ maskSize U) :
    Function.Surjective (fun c : zeroSubgroup (wordCode U) Z => restrictHom L c.val) :=
  minor_source_surjective_of_information_sets_le (wordCode U) (maskSize U)
    (wordCode_information_sets U)
    (by simpa only [Fintype.card_fin] using AESMixing.maskSize_le_four U) Z L hZL hdim

theorem wordMinor_card (U : Fin 16) (Z L : Fin 4 → Prop)
    (hZL : ∀ j, Z j → ¬ L j) (hZ : Fintype.card {j : Fin 4 // Z j} ≤ maskSize U)
    (hL : maskSize U - Fintype.card {j : Fin 4 // Z j} ≤
      Fintype.card {j : Fin 4 // L j}) :
    Fintype.card (wordMinor U Z L) =
      4294967296 ^ (maskSize U - Fintype.card {j : Fin 4 // Z j}) := by
  rw [minor_card_of_information_sets (wordCode U) (maskSize U)
    (wordCode_information_sets U) Z L hZL hZ hL, AES.word_card]
  norm_num

theorem remainingCoordinates_card (a : Fin 4) :
    Fintype.card {i : Fin 4 // i ≠ a} = 3 := by
  rw [Fintype.card_subtype_compl (fun i : Fin 4 => i = a),
    Fintype.card_fin, Fintype.card_subtype_eq]

/-- Single-coordinate shortening on the other three original physical legs. -/
abbrev shortenedWordCode (U : Fin 16) (a : Fin 4) :=
  wordMinor U (fun i => i = a) (fun i => i ≠ a)

/-- Single-coordinate puncturing on the same three physical legs. -/
abbrev puncturedWordCode (U : Fin 16) (a : Fin 4) :=
  wordMinor U (fun _ => False) (fun i => i ≠ a)

theorem shortenedWordCode_card (U : Fin 16) (a : Fin 4) (ht : 1 ≤ maskSize U) :
    Fintype.card (shortenedWordCode U a) = 4294967296 ^ (maskSize U - 1) := by
  have hfour := AESMixing.maskSize_le_four U
  simpa only [Fintype.card_subtype_eq] using
    wordMinor_card U (fun i => i = a) (fun i => i ≠ a)
      (by intro i hi hne; exact hne hi)
      (by simpa only [Fintype.card_subtype_eq] using ht)
      (by
        rw [Fintype.card_subtype_eq]
        have hrem : Nat.card {i : Fin 4 // i ≠ a} = 3 := by
          simpa only [← Nat.card_eq_fintype_card] using remainingCoordinates_card a
        have hcard (F : Fintype {i : Fin 4 // i ≠ a}) :
            @Fintype.card {i : Fin 4 // i ≠ a} F = 3 :=
          (@Nat.card_eq_fintype_card _ F).symm.trans hrem
        rw [hcard]
        omega)

theorem puncturedWordCode_card (U : Fin 16) (a : Fin 4) (ht : maskSize U ≤ 3) :
    Fintype.card (puncturedWordCode U a) = 4294967296 ^ maskSize U := by
  simpa using wordMinor_card U (fun _ => False) (fun i => i ≠ a)
    (by simp) (by simp) (by simpa [remainingCoordinates_card] using ht)

theorem shortenedWordCode_projection_bijective {A : Type*} [Fintype A]
    (U : Fin 16) (a : Fin 4) (ht : 1 ≤ maskSize U)
    (p : A → {i : Fin 4 // i ≠ a}) (hp : Function.Injective p)
    (hsize : Fintype.card A = maskSize U - 1) :
    Function.Bijective (fun c : shortenedWordCode U a => fun j : A => c.val (p j)) := by
  apply wordMinor_projection_bijective U (fun i => i = a) (fun i => i ≠ a)
    (by intro i hi hne; exact hne hi) p hp
  rw [Fintype.card_subtype_eq, hsize]
  omega

theorem puncturedWordCode_projection_bijective {A : Type*} [Fintype A]
    (U : Fin 16) (a : Fin 4)
    (p : A → {i : Fin 4 // i ≠ a}) (hp : Function.Injective p)
    (hsize : Fintype.card A = maskSize U) :
    Function.Bijective (fun c : puncturedWordCode U a => fun j : A => c.val (p j)) := by
  apply wordMinor_projection_bijective U (fun _ => False) (fun i => i ≠ a)
    (by simp) p hp
  simpa using hsize

end Word
end AESConcrete.ActivityMinorGeometry
