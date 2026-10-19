import AESMixing.ShortenedFibers

/-! MDS graph counts with arbitrary prescribed coordinate values.
An information-set bijection makes every compatible coordinate choice
uniform; no field structure beyond the already proved additive MDS
property is assumed. -/
noncomputable section
namespace AESMixing
open AES
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def graphPrescribed (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (u v : Fin 4 → V) (x : Fin 4 → V) : Prop :=
  (∀ i, maskBit r i = true → L x i = u i) ∧
    (∀ i, maskBit z i = true → x i = v i)

instance (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u v : Fin 4 → V) :
    DecidablePred (graphPrescribed L r z u v) := by
  intro x
  unfold graphPrescribed
  infer_instance

def informationTarget (r c : Fin 16) (u v : Fin 4 → V) : InformationIndex r c → V :=
  Sum.elim (fun i => u i.val) (fun i => v i.val)

omit [DecidableEq V] in
theorem graph_prescribed_iff_information
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c z : Fin 16) (hs : maskSize r = maskSize c)
    (hz : ∀ i, maskBit z i = true → maskBit c i ≠ true)
    (u v x : Fin 4 → V) :
    graphPrescribed L r z u v x ↔
      ∀ i, informationZero r c z i →
        mdsInformationEquiv L hL r c hs x i = informationTarget r c u v i := by
  constructor
  · rintro ⟨ho,hi⟩ (i | i) hp
    · exact ho i.val i.property
    · exact hi i.val hp
  · intro h
    constructor
    · intro i hi
      exact h (Sum.inl ⟨i,hi⟩) trivial
    · intro i hi
      exact h (Sum.inr ⟨i,hz i hi⟩) hi

theorem mds_graph_prescribed_count_low
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (hle : maskSize r+maskSize z ≤ 4) (u v : Fin 4 → V) :
    Fintype.card {x : Fin 4 → V // graphPrescribed L r z u v x} =
      Fintype.card V^(4-(maskSize r+maskSize z)) := by
  classical
  obtain ⟨c,hs,hz⟩ := low_mask_extension r z hle
  let e := mdsInformationEquiv L hL r c hs
  let p := informationZero r c z
  let target := informationTarget r c u v
  let restrictEquiv : {x : Fin 4 → V // graphPrescribed L r z u v x} ≃
      {x : Fin 4 → V // ∀ i, p i → e x i = target i} :=
    Equiv.subtypeEquivRight (fun x => graph_prescribed_iff_information L hL r c z hs hz u v x)
  rw [Fintype.card_congr restrictEquiv,
    Fintype.card_congr (pullbackConstraintEquiv e (fun f => ∀ i, p i → f i = target i)),
    prescribed_card]
  congr 1
  exact (Fintype.card_congr (freeInformationEquiv r c z)).trans
    (free_information_card r c z hs hz)

end AESMixing
