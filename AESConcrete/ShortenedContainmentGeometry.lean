import AESConcrete.ShortenedMixedGeometry

/-!
# Actual containment shifts on raw shortened graphs

When the line's three zero constraints contain the plane's two constraints,
the actual line point is also an actual plane point. Subtracting a plane
point from that included point is an involutive permutation of the raw
plane graph. Its marked difference identity gives the exact finite shift
interface used by the separate containment-pair analysis.

The line's canonical zero, nonzero marked coordinates, and cardinality are
derived from actual graph-coordinate bijections. Constructive scope only;
no response estimate, weight-enumerator premise, or word cap is proved here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedContainmentGeometry
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry
open AESConcrete.ShortenedMixedGeometry

set_option maxRecDepth 65536

/-- Reflection about the included actual line point, on the raw plane
graph. It needs no inferred group structure on the predicate subtype. -/
def shift (inverse : Bool) (out : Fin 16)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) :
    Equiv.Perm (ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2) where
  toFun w := subtractGraph (byteDiffusionHom inverse) q.val.1 q.val.2
    (containedGraph inverse out p q hcommon x) w
  invFun w := subtractGraph (byteDiffusionHom inverse) q.val.1 q.val.2
    (containedGraph inverse out p q hcommon x) w
  left_inv w := by
    apply Subtype.ext
    change x.val - (x.val-w.val) = w.val
    exact sub_sub_cancel _ _
  right_inv w := by
    apply Subtype.ext
    change x.val - (x.val-w.val) = w.val
    exact sub_sub_cancel _ _

theorem shift_val (inverse : Bool) (out : Fin 16)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2)
    (w : ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2) :
    (shift inverse out p q hcommon x w).val = x.val-w.val := rfl

/-- Exact actual marked-code shift identity. This is the geometric
interface, with original physical output labels unchanged. -/
theorem marked_shift_difference (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2)
    (w : ShortenedGraph (byteDiffusionHom inverse) q.val.1 q.val.2) :
    markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x -
        markedGraph (byteDiffusionHom inverse) q.val.1 q.val.2 (markedPositions e)
          (shift inverse out p q hcommon x w) =
      markedGraph (byteDiffusionHom inverse) q.val.1 q.val.2 (markedPositions e) w := by
  funext i
  change byteDiffusionHom inverse x.val (e i).val -
      byteDiffusionHom inverse (x.val-w.val) (e i).val = byteDiffusionHom inverse w.val (e i).val
  rw [map_sub]
  change byteDiffusionHom inverse x.val (e i).val -
      (byteDiffusionHom inverse x.val (e i).val - byteDiffusionHom inverse w.val (e i).val) =
    byteDiffusionHom inverse w.val (e i).val
  exact sub_sub_cancel _ _

theorem line_marked_zero (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) :
    markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)
      (zeroGraph (byteDiffusionHom inverse) p.val.1 p.val.2) = 0 :=
  markedGraph_zero _ _ _ _

/-- Every physical marked coordinate of a nonzero actual line point is
nonzero, by its coordinate equivalence and zero preservation. -/
theorem nonzero_line_marked_coordinate (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2)
    (hx : x ≠ zeroGraph (byteDiffusionHom inverse) p.val.1 p.val.2) (i : Fin 3) :
    markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x i ≠ 0 := by
  intro hi
  apply hx
  apply (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 p.property.2 (markedPositions e i) (marked_remaining e p i)).injective
  rw [coordinateEquiv_apply, coordinateEquiv_zero]
  exact hi

theorem raw_line_card (inverse : Bool) {out : Fin 16} (p : ShorteningChoice out 3) :
    Fintype.card (ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) = 256 := by
  rw [shortened_card (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 p.property.2]
  norm_num [BinaryWord.card]

end AESConcrete.ShortenedContainmentGeometry
