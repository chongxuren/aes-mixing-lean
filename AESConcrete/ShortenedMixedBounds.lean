import AESConcrete.ShortenedMixedGeometry
import AESConcrete.MixedCodeBounds
import AESConcrete.ActivityPlaneContraction

/-!
# Actual transverse line/plane response bound

This interface matches the actual graph difference bijection to the analytic
mixed-code estimate. Both response normalizations are inherited from the
physical shortened-code definitions. The common-zero premise is on actual
input/output masks. Constructive scope; containment and full word assembly
are distinct obligations.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ShortenedMixedBounds
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions marked_remaining)
open AESConcrete.ShortenedLineBounds
open AESConcrete.ShortenedPlaneResponse
open AESConcrete.ShortenedMixedGeometry
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)

theorem normalized_line_eq_code (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) T y =
      MixedCodeBounds.lineCodeResponse
        (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)) T y := by
  unfold normalizedResponse
  rw [action_codeIndicator _ _ (markedGraph_injective
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 p.property.2 (markedPositions e) (marked_remaining e p))]
  rfl

theorem normalized_plane_eq_code (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedPlaneResponse inverse e p T y =
      MixedCodeBounds.planeCodeResponse
        (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)) T y := by
  rw [ActivityPlaneContraction.normalized_plane_eq_shortened inverse out hout e]
  rfl

/-- Actual one-common-zero line/plane pair, including all normalizations. -/
theorem actual_line_plane_transverse_bound (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y| ≤ MixedCodeBounds.f3 := by
  simp_rw [normalized_line_eq_code, normalized_plane_eq_code inverse out hout e]
  exact MixedCodeBounds.actual_transverse_bound o _ _
    (zeroGraph _ p.val.1 p.val.2) (zeroGraph _ q.val.1 q.val.2)
    (markedGraph_zero _ _ _ _) (markedGraph_zero _ _ _ _)
    (differenceMap_bijective inverse out hout e p q hcommon)

theorem f3_lt_53_thousandths : MixedCodeBounds.f3 < (53 / 1000 : ℝ) := by
  norm_num [MixedCodeBounds.f3, LineOverlap.delta, LineOverlap.offdiag]

end AESConcrete.ShortenedMixedBounds
