import AESConcrete.MixedMarkedCoordinates
import AESConcrete.ShortenedMixedGeometry
import AESMixing.CoordinateCount

/-!
# Mixed physical line/plane difference and containment geometry

The selected triple may contain inputs and outputs. Transverse pairs use
equality on those actual physical coordinates; contained pairs use the
same raw graph point and its reflection in the plane. No analytic overlap
bound or desired block energy is assumed. Constructive mathematics only;
no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPairGeometry
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedCoordinates
open AESConcrete.ShortenedMixedGeometry (subtractGraph markedGraph_zero)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

-- The reused finite-mask lemmas depend only on zero masks and counts.
-- The empty output mask supplies their vacuous disjointness parameter;
-- no physical marked input is relabelled as an output.
theorem mixed_union_four (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 1) :
    maskSize (maskUnion r r') + maskSize (maskUnion z z') = 4 := by
  let p : ShorteningChoice 0 3 := ⟨(r,z), mask_disjoint_empty r, hline⟩
  let q : ShorteningChoice 0 2 := ⟨(r',z'), mask_disjoint_empty r', hplane⟩
  exact ShortenedMixedGeometry.mixed_union_four 0 p q hcommon

theorem plane_zeros_in_line (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 2) :
    (∀ i, maskBit r' i = true → maskBit r i = true) ∧
      (∀ i, maskBit z' i = true → maskBit z i = true) := by
  let p : ShorteningChoice 0 3 := ⟨(r,z), mask_disjoint_empty r, hline⟩
  let q : ShorteningChoice 0 2 := ⟨(r',z'), mask_disjoint_empty r', hplane⟩
  exact ShortenedMixedGeometry.plane_zeros_in_line 0 p q hcommon

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def differenceMap (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z r' z' : Fin 16)
    (marked : Fin 3 → GraphPosition)
    (x : ShortenedGraph L r z × ShortenedGraph L r' z') : Fin 3 → V :=
  markedGraph L r z marked x.1 - markedGraph L r' z' marked x.2

theorem differenceMap_zero (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z r' z' : Fin 16)
    (marked : Fin 3 → GraphPosition) :
    differenceMap L r z r' z' marked (zeroGraph L r z,zeroGraph L r' z') = 0 := by
  simp only [differenceMap, markedGraph_zero, sub_self]

theorem differenceMap_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z r' z' : Fin 16)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i))
    (hcommon : 1 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z')) :
    Function.Injective (differenceMap L r z r' z' marked) := by
  intro x y hxy
  let a := subtractGraph L r z x.1 y.1
  let b := subtractGraph L r' z' x.2 y.2
  have heq (i : Fin 3) : graphCoordinate L a.val (marked i) = graphCoordinate L b.val (marked i) := by
    have hh := congrFun hxy i
    change graphCoordinate L x.1.val (marked i) - graphCoordinate L x.2.val (marked i) =
      graphCoordinate L y.1.val (marked i) - graphCoordinate L y.2.val (marked i) at hh
    change graphCoordinate L (x.1.val-y.1.val) (marked i) =
      graphCoordinate L (x.2.val-y.2.val) (marked i)
    rw [graphCoordinate_sub, graphCoordinate_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hh
  have hab := selected_points_equal L hL r z r' z' marked hmarked
    (fun i => remaining_common r z r' z' (marked i) (hm i))
    (by simp only [Fintype.card_fin]; omega) a b heq
  have ha := equal_points_zero_of_union L hL r z r' z' hunion a b hab
  have hb : b.val = 0 := hab.symm.trans ha
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp ha
  · apply Subtype.ext
    exact sub_eq_zero.mp hb

theorem differenceMap_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i))
    (hcommon : 1 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z')) :
    Function.Bijective (differenceMap L r z r' z' marked) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨differenceMap_injective L hL r z r' z' marked hmarked hm hcommon hunion, ?_⟩
  rw [Fintype.card_prod, mds_graph_zero_count L hL, mds_graph_zero_count L hL,
    hline, hplane, Fintype.card_fun, Fintype.card_fin]
  simp only [Nat.reduceSub, pow_one]
  ring

def containedGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z r' z' : Fin 16)
    (hcontains : (∀ i, maskBit r' i = true → maskBit r i = true) ∧
      (∀ i, maskBit z' i = true → maskBit z i = true))
    (x : ShortenedGraph L r z) : ShortenedGraph L r' z' :=
  ⟨x.val, ⟨fun i hi => x.property.1 i (hcontains.1 i hi),
    fun i hi => x.property.2 i (hcontains.2 i hi)⟩⟩

def shift (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z r' z' : Fin 16)
    (hcontains : (∀ i, maskBit r' i = true → maskBit r i = true) ∧
      (∀ i, maskBit z' i = true → maskBit z i = true))
    (x : ShortenedGraph L r z) : Equiv.Perm (ShortenedGraph L r' z') where
  toFun w := subtractGraph L r' z' (containedGraph L r z r' z' hcontains x) w
  invFun w := subtractGraph L r' z' (containedGraph L r z r' z' hcontains x) w
  left_inv w := by
    apply Subtype.ext
    change x.val-(x.val-w.val) = w.val
    exact sub_sub_cancel _ _
  right_inv w := by
    apply Subtype.ext
    change x.val-(x.val-w.val) = w.val
    exact sub_sub_cancel _ _

theorem marked_shift_difference (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z r' z' : Fin 16) (marked : Fin 3 → GraphPosition)
    (hcontains : (∀ i, maskBit r' i = true → maskBit r i = true) ∧
      (∀ i, maskBit z' i = true → maskBit z i = true))
    (x : ShortenedGraph L r z) (w : ShortenedGraph L r' z') :
    markedGraph L r z marked x -
        markedGraph L r' z' marked (shift L r z r' z' hcontains x w) =
      markedGraph L r' z' marked w := by
  funext i
  change graphCoordinate L x.val (marked i) -
    graphCoordinate L (x.val-w.val) (marked i) = graphCoordinate L w.val (marked i)
  rw [graphCoordinate_sub]
  exact sub_sub_cancel _ _

theorem nonzero_line_marked_coordinate
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hline : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (x : ShortenedGraph L r z)
    (hx : x ≠ zeroGraph L r z) (i : Fin 3) : markedGraph L r z marked x i ≠ 0 := by
  intro hi
  apply hx
  apply (coordinateEquiv L hL r z hline (marked i) (hm i)).injective
  rw [coordinateEquiv_apply, coordinateEquiv_apply]
  exact hi.trans (graphCoordinate_zero L (marked i)).symm

def pairPositions (marked : Fin 3 → GraphPosition) (i j : Fin 3) : Fin 2 → GraphPosition :=
  fun k => if k = 0 then marked i else marked j

theorem pairPositions_injective (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (i j : Fin 3) (hij : i ≠ j) :
    Function.Injective (pairPositions marked i j) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact (hij (hmarked (by simpa [pairPositions] using hab))).elim
  · exact (hij (hmarked (by simpa [pairPositions] using hab.symm))).elim
  · rfl

theorem pairPositions_remaining (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i j : Fin 3) (k : Fin 2) :
    remaining r z (pairPositions marked i j k) := by
  fin_cases k
  · simpa [pairPositions] using hm i
  · simpa [pairPositions] using hm j

theorem marked_zero_fiber_card
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    Fintype.card {x : ShortenedGraph L r z // markedGraph L r z marked x i = 0} = Fintype.card V := by
  obtain ⟨j,hj⟩ := exists_ne i
  let selected := pairPositions marked i j
  have hb := ActualMarkedCodeMoment.selected_projection_bijective L hL r z selected
    (pairPositions_injective marked hmarked i j hj.symm)
    (pairPositions_remaining r z marked hm i j) (by simp only [Fintype.card_fin]; omega)
  let e := Equiv.ofBijective (fun x : ShortenedGraph L r z =>
    fun k : Fin 2 => graphCoordinate L x.val (selected k)) hb
  have he (x : ShortenedGraph L r z) : markedGraph L r z marked x i = 0 ↔
      ∀ k : Fin 2, k = 0 → e x k = 0 := by
    constructor
    · intro hx k hk
      subst k
      simpa [e, selected, pairPositions, markedGraph] using hx
    · intro hx
      simpa [e, selected, pairPositions, markedGraph] using hx 0 rfl
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have hc := bijective_prescribed_card e (fun k : Fin 2 => k = 0) (fun _ => (0 : V))
  -- The two logically identical finite forall predicates synthesize
  -- different decidability instances. Nat.card removes that implementation
  -- choice before the actual fiber cardinalities are compared.
  have hn : Nat.card {k : Fin 2 // ¬ k = 0} = 1 := by
    simpa only [Nat.card_eq_fintype_card] using
      (show Fintype.card {k : Fin 2 // ¬ k = 0} = 1 by decide)
  simpa only [← Nat.card_eq_fintype_card, hn, pow_one] using hc

theorem two_marked_zeros_force_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (x : ShortenedGraph L r z) (i j : Fin 3) (hij : i ≠ j)
    (hi : markedGraph L r z marked x i = 0) (hj : markedGraph L r z marked x j = 0) :
    x = zeroGraph L r z := by
  let selected := pairPositions marked i j
  have he : (fun k : Fin 2 => graphCoordinate L x.val (selected k)) =
      fun k : Fin 2 => graphCoordinate L (zeroGraph L r z).val (selected k) := by
    funext k
    fin_cases k
    · simpa [selected, pairPositions, markedGraph, zeroGraph, graphCoordinate] using hi
    · simpa [selected, pairPositions, markedGraph, zeroGraph, graphCoordinate] using hj
  exact ActualMarkedCodeMoment.selected_projection_injective L hL r z selected
    (pairPositions_injective marked hmarked i j hij)
    (pairPositions_remaining r z marked hm i j)
    (by simp only [Fintype.card_fin]; omega) he

end Generic
end AESConcrete.MixedMarkedPairGeometry
