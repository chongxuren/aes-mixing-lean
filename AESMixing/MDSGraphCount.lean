import AESMixing.CoordinateCount
import AESMixing.MaskSelections
import Mathlib.Logic.Equiv.Prod

/-! Exact shortening counts for the graph of an additive four-coordinate MDS map.
Zero constraints on any input/output positions leave m^(4-number of constraints)
points up to four constraints, and only the zero point beyond that threshold. -/
noncomputable section
namespace AESMixing
open AES

abbrev InformationIndex (r c : Fin 16) := MaskCoordinates r ⊕ ComplementCoordinates c

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def mdsInformationEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hs : maskSize r = maskSize c) :
    (Fin 4 → V) ≃ (InformationIndex r c → V) :=
  (Equiv.ofBijective (mdsInformation L r c) (mds_information_bijective L hL r c hs)).trans
    (Equiv.sumArrowEquivProdArrow (MaskCoordinates r) (ComplementCoordinates c) V).symm

omit [Fintype V] [DecidableEq V] in
def graphZeroConditions (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (x : Fin 4 → V) : Prop :=
  (∀ i, maskBit r i = true → L x i = 0) ∧
  (∀ i, maskBit z i = true → x i = 0)

instance (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    DecidablePred (graphZeroConditions L r z) := by
  intro x
  unfold graphZeroConditions
  infer_instance

def informationZero (r c z : Fin 16) : InformationIndex r c → Prop :=
  Sum.elim (fun _ => True) (fun i => maskBit z i.val = true)

instance (r c z : Fin 16) : DecidablePred (informationZero r c z) := by
  intro i
  cases i <;> unfold informationZero <;> dsimp <;> infer_instance

omit [DecidableEq V] in
theorem graph_zero_iff_information (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r c z : Fin 16) (hs : maskSize r = maskSize c)
    (hz : ∀ i, maskBit z i = true → maskBit c i ≠ true) (x : Fin 4 → V) :
    graphZeroConditions L r z x ↔
      ∀ i, informationZero r c z i → mdsInformationEquiv L hL r c hs x i = 0 := by
  constructor
  · rintro ⟨ho, hi⟩ (i | i) hp
    · exact ho i.val i.property
    · exact hi i.val hp
  · intro h
    constructor
    · intro i hi
      exact h (Sum.inl ⟨i,hi⟩) trivial
    · intro i hi
      exact h (Sum.inr ⟨i,hz i hi⟩) hi

def freeInformationEquiv (r c z : Fin 16) :
    {i : InformationIndex r c // ¬ informationZero r c z i} ≃
      {i : Fin 4 // maskBit c i ≠ true ∧ maskBit z i ≠ true} where
  toFun i := match i with
    | ⟨Sum.inl _, h⟩ => False.elim (h trivial)
    | ⟨Sum.inr j, h⟩ => ⟨j.val, j.property, h⟩
  invFun i := ⟨Sum.inr ⟨i.val, i.property.1⟩, i.property.2⟩
  left_inv i := by
    rcases i with ⟨i | i,h⟩
    · exact False.elim (h trivial)
    · rfl
  right_inv _ := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem free_information_card : ∀ r c z : Fin 16,
    maskSize r = maskSize c →
    (∀ i : Fin 4, maskBit z i = true → maskBit c i ≠ true) →
    Fintype.card {i : Fin 4 // maskBit c i ≠ true ∧ maskBit z i ≠ true} =
      4 - (maskSize r + maskSize z) := by
  decide

theorem mds_graph_zero_count_low (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) (hle : maskSize r + maskSize z ≤ 4) :
    Fintype.card {x : Fin 4 → V // graphZeroConditions L r z x} =
      Fintype.card V ^ (4 - (maskSize r + maskSize z)) := by
  classical
  obtain ⟨c,hs,hz⟩ := low_mask_extension r z hle
  let e := mdsInformationEquiv L hL r c hs
  let p := informationZero r c z
  let restrictEquiv : {x : Fin 4 → V // graphZeroConditions L r z x} ≃
      {x : Fin 4 → V // ∀ i, p i → e x i = 0} :=
    Equiv.subtypeEquivRight (fun x => graph_zero_iff_information L hL r c z hs hz x)
  rw [Fintype.card_congr restrictEquiv,
    Fintype.card_congr (pullbackConstraintEquiv e (fun f => ∀ i, p i → f i = 0)),
    zero_restricted_card]
  congr 1
  exact (Fintype.card_congr (freeInformationEquiv r c z)).trans
    (free_information_card r c z hs hz)

omit [Fintype V] [DecidableEq V] in
theorem mds_graph_zero_high (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) (hle : 4 ≤ maskSize r + maskSize z)
    (x : Fin 4 → V) (hx : graphZeroConditions L r z x) : x = 0 := by
  obtain ⟨r',c,hs,hr,hc⟩ := high_mask_restriction r z hle
  apply mds_information_injective L hL r' c hs
  apply Prod.ext
  · funext i
    change L x i.val = L 0 i.val
    rw [map_zero]
    exact hx.1 i.val (hr i.val i.property)
  · funext i
    exact hx.2 i.val (hc i.val i.property)

theorem mds_graph_zero_count (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) :
    Fintype.card {x : Fin 4 → V // graphZeroConditions L r z x} =
      Fintype.card V ^ (4 - (maskSize r + maskSize z)) := by
  classical
  by_cases h : maskSize r + maskSize z ≤ 4
  · exact mds_graph_zero_count_low L hL r z h
  · have hh : 4 ≤ maskSize r + maskSize z := Nat.le_of_lt (Nat.lt_of_not_ge h)
    have hz : graphZeroConditions L r z 0 := by
      constructor <;> intro i _ <;> simp
    letI : Unique {x : Fin 4 → V // graphZeroConditions L r z x} :=
      { default := ⟨0,hz⟩
        uniq := fun x => Subtype.ext (mds_graph_zero_high L hL r z hh x.val x.property) }
    simp [Nat.sub_eq_zero_of_le hh]

end AESMixing
