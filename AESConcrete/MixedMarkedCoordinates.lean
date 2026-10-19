import AESConcrete.ActualMarkedCodeMoment

/-!
# Equality of actual shortened graph points from mixed physical coordinates

Selected coordinates may be inputs, outputs, or a mixture. Equal selected
coordinates of two shortened points force their difference to vanish once
their common zero constraints and selected coordinates contain an MDS
information set. This replaces the output-only equality interface; it does
not rename input positions into output positions. Constructive mathematics
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
namespace AESConcrete.MixedMarkedCoordinates
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse

section Generic
variable {V I : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V] [Fintype I]

theorem graphCoordinate_zero (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : GraphPosition) :
    graphCoordinate L 0 p = 0 := by
  cases p <;> simp [graphCoordinate]

theorem graphCoordinate_sub (L : (Fin 4 → V) →+ (Fin 4 → V))
    (x y : Fin 4 → V) (p : GraphPosition) :
    graphCoordinate L (x-y) p = graphCoordinate L x p - graphCoordinate L y p := by
  cases p <;> simp [graphCoordinate, map_sub]

theorem remaining_common (r z r' z' : Fin 16) (p : GraphPosition)
    (hp : remaining r z p) :
    remaining (maskIntersection r r') (maskIntersection z z') p := by
  cases p with
  | inl i =>
    intro h
    rw [maskIntersection_bit, Bool.and_eq_true] at h
    exact hp h.1
  | inr i =>
    intro h
    rw [maskIntersection_bit, Bool.and_eq_true] at h
    exact hp h.1

def commonDifference (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z r' z' : Fin 16)
    (x : ShortenedGraph L r z) (y : ShortenedGraph L r' z') :
    ShortenedGraph L (maskIntersection r r') (maskIntersection z z') :=
  ⟨x.val-y.val, by
    constructor
    · intro i hi
      rw [maskIntersection_bit, Bool.and_eq_true] at hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      rw [x.property.1 i hi.1, y.property.1 i hi.2, sub_self]
    · intro i hi
      rw [maskIntersection_bit, Bool.and_eq_true] at hi
      change x.val i - y.val i = 0
      rw [x.property.2 i hi.1, y.property.2 i hi.2, sub_self]⟩

/-- The selected positions retain their actual physical input/output tags. -/
theorem selected_points_equal
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z r' z' : Fin 16) (selected : I → GraphPosition)
    (hselected : Function.Injective selected)
    (hfree : ∀ i, remaining (maskIntersection r r') (maskIntersection z z') (selected i))
    (hsize : 4 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z') + Fintype.card I)
    (x : ShortenedGraph L r z) (y : ShortenedGraph L r' z')
    (heq : ∀ i, graphCoordinate L x.val (selected i) = graphCoordinate L y.val (selected i)) :
    x.val = y.val := by
  let d := commonDifference L r z r' z' x y
  let o := zeroGraph L (maskIntersection r r') (maskIntersection z z')
  have he : (fun i : I => graphCoordinate L d.val (selected i)) =
      fun i : I => graphCoordinate L o.val (selected i) := by
    funext i
    change graphCoordinate L (x.val-y.val) (selected i) = graphCoordinate L 0 (selected i)
    rw [graphCoordinate_sub, heq i, sub_self, graphCoordinate_zero]
  have hd := ActualMarkedCodeMoment.selected_projection_injective L hL
    (maskIntersection r r') (maskIntersection z z') selected hselected hfree hsize he
  have hv := congrArg Subtype.val hd
  change x.val-y.val = 0 at hv
  exact sub_eq_zero.mp hv

theorem equal_points_zero_of_union
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z r' z' : Fin 16)
    (hsize : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z'))
    (x : ShortenedGraph L r z) (y : ShortenedGraph L r' z')
    (hxy : x.val = y.val) : x.val = 0 := by
  apply mds_graph_zero_high L hL (maskUnion r r') (maskUnion z z') hsize x.val
  constructor
  · intro i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact x.property.1 i hi
    · rw [hxy]
      exact y.property.1 i hi
  · intro i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact x.property.2 i hi
    · rw [hxy]
      exact y.property.2 i hi

end Generic
end AESConcrete.MixedMarkedCoordinates
