import AESMixing.ShortenedMDS

/-! Fiber bounds for marked coordinates of a shortened MDS graph.
Subtracting any one solution maps its whole fiber injectively into the
graph with the marked coordinates also set to zero. The exact zero count
then bounds every prescribed assignment, including inconsistent ones. -/
noncomputable section
namespace AESMixing
open AES
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem shortened_projection_fiber_bound
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (v : (MaskCoordinates out → V) × (MaskCoordinates inp → V)) :
    Fintype.card {x : ShortenedGraph L r z // shortenedProjection L r z out inp x = v} ≤
      Fintype.card V ^ (4-(maskSize r+maskSize z+maskSize out+maskSize inp)) := by
  classical
  let X := {x : ShortenedGraph L r z // shortenedProjection L r z out inp x = v}
  by_cases hzero : Fintype.card X = 0
  · change Fintype.card X ≤ _
    rw [hzero]
    exact Nat.zero_le _
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  have hsub (x : X) : graphZeroConditions L (maskUnion r out) (maskUnion z inp)
      (x.val.val-x₀.val.val) := by
    constructor
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rw [map_sub]
      change L x.val.val i-L x₀.val.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.val.property.1 i hi, x₀.val.property.1 i hi]
      · exact congrFun (congrArg Prod.fst (x.property.trans x₀.property.symm))
          (⟨i,hi⟩ : MaskCoordinates out)
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      change x.val.val i-x₀.val.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.val.property.2 i hi, x₀.val.property.2 i hi]
      · exact congrFun (congrArg Prod.snd (x.property.trans x₀.property.symm))
          (⟨i,hi⟩ : MaskCoordinates inp)
  let e : X → ShortenedGraph L (maskUnion r out) (maskUnion z inp) :=
    fun x => ⟨x.val.val-x₀.val.val,hsub x⟩
  have he : Function.Injective e := by
    intro x y h
    have hv := congrArg Subtype.val h
    change x.val.val-x₀.val.val = y.val.val-x₀.val.val at hv
    exact Subtype.ext (Subtype.ext (sub_left_inj.mp hv))
  have hc := Fintype.card_le_of_injective e he
  rw [mds_graph_zero_count L hL, maskUnion_size r out hr, maskUnion_size z inp hz] at hc
  have hn : maskSize r+maskSize out+(maskSize z+maskSize inp) =
      maskSize r+maskSize z+maskSize out+maskSize inp := by omega
  rw [hn] at hc
  exact hc

end AESMixing
