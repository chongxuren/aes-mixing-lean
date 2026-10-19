import AESConcrete.ShortenedPlane

/-!
# Actual line/plane difference geometry

For a three-zero line and a two-zero plane sharing exactly one physical
zero constraint, the actual marked difference map is injective: equal
marked differences identify two graph differences by their common zero,
and the four union zeros then force both differences to vanish. Exact
MDS graph cardinalities make this map bijective onto the marked triple.

If both plane zero constraints are shared, the line graph embeds into the
plane graph with the same underlying physical input. The corresponding
marked line is therefore contained in the actual marked plane.

Constructive scope only. Analytic f3 and z3/h3 bounds and their response
wrappers belong to separate modules; no frozen source is changed here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedMixedGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry
open AESConcrete.ShortenedPlane

set_option maxRecDepth 65536

private theorem union_inter_size : ∀ r s : Fin 16,
    maskSize (maskUnion r s) + maskSize (maskIntersection r s) = maskSize r + maskSize s := by decide
private theorem inter_le_right : ∀ r s : Fin 16, maskSize (maskIntersection r s) ≤ maskSize s := by decide
private theorem inter_eq_right : ∀ r s : Fin 16,
    maskSize (maskIntersection r s) = maskSize s → maskIntersection r s = s := by decide

section GraphOperations
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def subtractGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (x y : ShortenedGraph L r z) : ShortenedGraph L r z :=
  ⟨x.val-y.val, by
    constructor
    · intro i hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      rw [x.property.1 i hi, y.property.1 i hi, sub_self]
    · intro i hi
      change x.val i - y.val i = 0
      rw [x.property.2 i hi, y.property.2 i hi, sub_self]⟩

theorem markedGraph_zero (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (marked : Fin 3 → GraphPosition) : markedGraph L r z marked (zeroGraph L r z) = 0 := by
  funext i
  cases h : marked i <;> simp [markedGraph, zeroGraph, graphCoordinate, h]

end GraphOperations

def differenceMap (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 ×
      ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2) : Fin 3 → Byte :=
  markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x.1 -
    markedGraph (byteDiffusionHom inverse) q.val.1 q.val.2 (markedPositions e) x.2

theorem differenceMap_zero (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2) :
    differenceMap inverse e p q (zeroGraph _ p.val.1 p.val.2, zeroGraph _ q.val.1 q.val.2) = 0 := by
  simp only [differenceMap, markedGraph_zero, sub_self]

theorem mixed_union_four (out : Fin 16) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) :
    maskSize (maskUnion p.val.1 q.val.1) + maskSize (maskUnion p.val.2 q.val.2) = 4 := by
  have h1 := union_inter_size p.val.1 q.val.1
  have h2 := union_inter_size p.val.2 q.val.2
  have hp := p.property.2
  have hq := q.property.2
  omega

/-- Actual transverse line/plane difference injection. No code dimension
or assumed distinct-output representation is a premise. -/
theorem differenceMap_injective (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) :
    Function.Injective (differenceMap inverse e p q) := by
  intro x y hxy
  let a := subtractGraph (byteDiffusionHom inverse) p.val.1 p.val.2 x.1 y.1
  let b := subtractGraph (byteDiffusionHom inverse) q.val.1 q.val.2 x.2 y.2
  have hd : MaskDisjoint (maskIntersection p.val.1 q.val.1) out := by
    intro i hi ho
    simp only [maskIntersection_bit, Bool.and_eq_true] at hi
    exact p.property.1 i hi.1 ho
  have heq (i : Fin 4) (hi : maskBit out i = true) :
      byteDiffusionHom inverse a.val i = byteDiffusionHom inverse b.val i := by
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
    have hv : (e j).val = i := congrArg Subtype.val hj
    have hh := congrFun hxy j
    change byteDiffusionHom inverse x.1.val (e j).val - byteDiffusionHom inverse x.2.val (e j).val =
      byteDiffusionHom inverse y.1.val (e j).val - byteDiffusionHom inverse y.2.val (e j).val at hh
    have hs := sub_eq_sub_iff_sub_eq_sub.mp hh
    change byteDiffusionHom inverse (x.1.val-y.1.val) i =
      byteDiffusionHom inverse (x.2.val-y.2.val) i
    simp only [map_sub, Pi.sub_apply]
    simpa only [hv] using hs
  have hab := shortened_points_equal (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 q.val.1 q.val.2 out hd (by omega) a b heq
  have hazero : a.val = 0 := by
    apply mds_graph_zero_high (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (maskUnion p.val.1 q.val.1) (maskUnion p.val.2 q.val.2)
      (by rw [mixed_union_four out p q hcommon]) a.val
    apply graph_zeros_union
    · exact a.property
    · rw [hab]
      exact b.property
  have hbzero : b.val = 0 := by rw [← hab]; exact hazero
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hazero
  · apply Subtype.ext
    exact sub_eq_zero.mp hbzero

/-- Exact graph cardinalities turn the actual difference injection into
a bijection onto all three physical marked bytes. -/
theorem differenceMap_bijective (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) :
    Function.Bijective (differenceMap inverse e p q) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨differenceMap_injective inverse out hout e p q hcommon, ?_⟩
  rw [Fintype.card_prod,
    shortened_card (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      p.val.1 p.val.2 p.property.2,
    plane_choice_cardinality (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) out q]
  norm_num [Fintype.card_fun, BinaryWord.card]

/-- With two common zeros, every zero prescribed by the plane is also
prescribed by the line. This is actual mask containment. -/
theorem plane_zeros_in_line (out : Fin 16) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) :
    (∀ i, maskBit q.val.1 i = true → maskBit p.val.1 i = true) ∧
      (∀ i, maskBit q.val.2 i = true → maskBit p.val.2 i = true) := by
  have h1 := inter_le_right p.val.1 q.val.1
  have h2 := inter_le_right p.val.2 q.val.2
  have hq := q.property.2
  have he1 : maskSize (maskIntersection p.val.1 q.val.1) = maskSize q.val.1 := by omega
  have he2 : maskSize (maskIntersection p.val.2 q.val.2) = maskSize q.val.2 := by omega
  have hm1 := inter_eq_right p.val.1 q.val.1 he1
  have hm2 := inter_eq_right p.val.2 q.val.2 he2
  constructor
  · intro i hi
    have hh : maskBit (maskIntersection p.val.1 q.val.1) i = true := by rw [hm1]; exact hi
    simp only [maskIntersection_bit, Bool.and_eq_true] at hh
    exact hh.1
  · intro i hi
    have hh : maskBit (maskIntersection p.val.2 q.val.2) i = true := by rw [hm2]; exact hi
    simp only [maskIntersection_bit, Bool.and_eq_true] at hh
    exact hh.1

def containedGraph (inverse : Bool) (out : Fin 16)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) :
    ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2 :=
  ⟨x.val, by
    have hs := plane_zeros_in_line out p q hcommon
    exact ⟨fun i hi => x.property.1 i (hs.1 i hi), fun i hi => x.property.2 i (hs.2 i hi)⟩⟩

theorem containedGraph_injective (inverse : Bool) (out : Fin 16)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) :
    Function.Injective (containedGraph inverse out p q hcommon) := by
  intro x y hxy
  apply Subtype.ext
  have hv := congrArg
    (fun u : ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2 => u.val) hxy
  change x.val = y.val at hv
  exact hv

theorem marked_line_mem_plane (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) :
    markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x ∈ plane inverse e q := by
  let y := containedGraph inverse out p q hcommon x
  change ∃ u : graphSubgroup inverse q.val.1 q.val.2,
    projectionHom inverse q.val.1 q.val.2 e u = _
  exact ⟨⟨y.val, y.property⟩, rfl⟩

end AESConcrete.ShortenedMixedGeometry
