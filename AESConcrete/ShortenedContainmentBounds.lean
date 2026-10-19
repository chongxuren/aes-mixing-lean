import AESConcrete.ShortenedMixedBounds
import AESConcrete.ShortenedContainmentGeometry
import AESConcrete.ShortenedPlaneWeights
import AESConcrete.ContainmentCodeBounds

/-!
# Actual AES containment line/plane interval

The actual two-common-zero pair supplies every geometric premise of the
analytic containment estimate. Its signed normalized overlap is within h3
of z3. This is a shortened-response theorem; the full centered word operator
and effective input metric are separate obligations.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ShortenedContainmentBounds
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineBounds
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ShortenedPlaneResponse
open AESConcrete.ShortenedMixedGeometry (markedGraph_zero)
open AESConcrete.ShortenedMixedBounds
open AESConcrete.ShortenedContainmentGeometry
open AESConcrete.ShortenedPlaneWeights
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.ContainmentCodeBounds (z3 h3)
set_option maxRecDepth 65536

theorem actual_line_plane_containment_bound (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) (o : Fin 3 → Orientation) :
    |(4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y) - z3| ≤ h3 := by
  simp_rw [normalized_line_eq_code, normalized_plane_eq_code inverse out hout e]
  apply ContainmentCodeBounds.actual_containment_bound o _ _
    (zeroGraph _ p.val.1 p.val.2) (zeroGraph _ q.val.1 q.val.2)
    (markedGraph_zero _ _ _ _) (markedGraph_zero _ _ _ _)
    (raw_line_card inverse p) (raw_plane_card inverse q)
    (nonzero_line_marked_coordinate inverse e p)
    (marked_zero_fiber_card inverse e q)
    (two_marked_zeros_force_zero inverse out hout e q)
    (shift inverse out p q hcommon)
  intro x w i
  exact congrFun (marked_shift_difference inverse out e p q hcommon x w) i

theorem actual_line_plane_containment_interval (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) (o : Fin 3 → Orientation) :
    z3-h3 ≤ (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y) ∧
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y) ≤ z3+h3 := by
  have h := abs_le.mp (actual_line_plane_containment_bound inverse out hout e p q hcommon o)
  constructor <;> linarith [h.1, h.2]

theorem z3_bounds : (67 / 1000 : ℝ) < z3 ∧ z3 < (68 / 1000 : ℝ) := by
  norm_num [z3, LineOverlap.delta]

theorem h3_lt_49_thousandths : h3 < (49 / 1000 : ℝ) := by
  norm_num [h3, LineOverlap.delta, LineOverlap.offdiag]

end AESConcrete.ShortenedContainmentBounds
