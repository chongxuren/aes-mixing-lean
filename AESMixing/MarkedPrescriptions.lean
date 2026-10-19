import AESMixing.MDSPrescribedCount
import AESMixing.ShortenedIncidence

/-! Exact marked-coordinate marginals of a shortened MDS graph. At most
the remaining dimension's worth of prescribed coordinates has a uniform
joint marginal. This is the counting premise for residual cancellation. -/
noncomputable section
namespace AESMixing
open AES

theorem zero_marked_iff {V : Type*} [Zero V]
    (r s : Fin 16) (hrs : MaskDisjoint r s)
    (f : Fin 4 → V) (v : MaskCoordinates s → V) :
    ((∀ i, maskBit r i = true → f i = 0) ∧ (∀ i : MaskCoordinates s, f i.val = v i)) ↔
      ∀ i, maskBit (maskUnion r s) i = true → f i = extendCoordinates s v i := by
  constructor
  · rintro ⟨hz,hv⟩ i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · rw [hz i hi]
      simp [extendCoordinates, hrs i hi]
    · simpa only [extendCoordinates, hi, dite_true] using hv ⟨i,hi⟩
  · intro h
    constructor
    · intro i hi
      have hh := h i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
      simpa [extendCoordinates, hrs i hi] using hh
    · intro i
      have hh := h i.val (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr i.property)
      simpa only [extendCoordinates, i.property, dite_true] using hh

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
def shortened_prescribed_equiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    {x : ShortenedGraph L r z // shortenedProjection L r z out inp x = (y,w)} ≃
      {x : Fin 4 → V // graphPrescribed L (maskUnion r out) (maskUnion z inp)
        (extendCoordinates out y) (extendCoordinates inp w) x} where
  toFun x := ⟨x.val.val,
    (zero_marked_iff r out hr (L x.val.val) y).mp
      ⟨x.val.property.1, fun i => congrFun (congrArg Prod.fst x.property) i⟩,
    (zero_marked_iff z inp hz x.val.val w).mp
      ⟨x.val.property.2, fun i => congrFun (congrArg Prod.snd x.property) i⟩⟩
  invFun x := by
    have ho := (zero_marked_iff r out hr (L x.val) y).mpr x.property.1
    have hi := (zero_marked_iff z inp hz x.val w).mpr x.property.2
    exact ⟨⟨x.val,ho.1,hi.1⟩,Prod.ext (funext ho.2) (funext hi.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem shortened_projection_fiber_uniform
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (ht : maskSize r+maskSize z+maskSize out+maskSize inp ≤ 4)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    Fintype.card {x : ShortenedGraph L r z // shortenedProjection L r z out inp x = (y,w)} =
      Fintype.card V^(4-(maskSize r+maskSize z+maskSize out+maskSize inp)) := by
  classical
  have hsize : maskSize (maskUnion r out)+maskSize (maskUnion z inp) =
      maskSize r+maskSize z+maskSize out+maskSize inp := by
    rw [maskUnion_size r out hr, maskUnion_size z inp hz]
    omega
  rw [Fintype.card_congr (shortened_prescribed_equiv L r z out inp hr hz y w),
    mds_graph_prescribed_count_low L hL _ _ (by rw [hsize]; exact ht), hsize]

end AESMixing
