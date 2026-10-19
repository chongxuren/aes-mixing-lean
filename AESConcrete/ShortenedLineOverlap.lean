import AESConcrete.ShortenedLineGeometry
import AESConcrete.ShortenedLineBounds

/-!
# Actual shortened-code overlap bounds

This interface closes the geometry-to-ratio-to-response chain for ordinary
three-leg responses. The coefficients, their nonzero proofs, and their ratio
separation all come from the actual forward/inverse AES shortening. No slope
representation or overlap-count premise is supplied by the caller. The
responses remain the product action on actual projected-code indicators,
divided by 256; the outer word factor is explicitly 2^32.

Constructive scope only. Fourier plane responses and the word activity-frame
assembly are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedLineOverlap
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedByteLinearity
open AESConcrete.ShortenedLineGeometry
open AESConcrete.ShortenedLineBounds
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)

/-- The semantic line parameters equal the field slopes derived from the
actual physical byte matrix. -/
theorem coordinatePerm_eq_slope (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3) :
    lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        p.val.1 p.val.2 p.property.2 (markedPositions e) (marked_remaining e p) =
      LineOverlap.slopeEquiv (coefficient inverse e p) (coefficient_nonzero inverse e p) := by
  funext i
  exact lineCoordinatePerm_eq_mulLeft inverse p.val.1 p.val.2 p.property.2
    (markedPositions e) (marked_remaining e p) i

theorem normalizedResponse_eq_slope (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 3)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) T y =
      DampedLineGram.lineResponse T
        (LineOverlap.slopeEquiv (coefficient inverse e p) (coefficient_nonzero inverse e p)) y := by
  rw [normalizedResponse_eq_line inverse p.val.1 p.val.2 p.property.2
    (markedPositions e) (marked_remaining e p), coordinatePerm_eq_slope]

/-- Distinct actual one-parameter shortenings supply the eta2 case, with
no unproved line-representation or ratio hypothesis. -/
theorem actual_shortened_line_pair_eta2 (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 3) (hpq : p ≠ q) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedResponse inverse q.val.1 q.val.2 (markedPositions e) (fun i => leg (o i) false) y| ≤
      LineOverlap.eta2 := by
  simp_rw [normalizedResponse_eq_slope]
  exact LineOverlap.actual_line_pair_eta2 o (coefficient inverse e p) (coefficient inverse e q)
    (coefficient_nonzero inverse e p) (coefficient_nonzero inverse e q)
    (distinct_choices_ratios_nonconstant inverse out hout e p q hpq)

/-- Two common physical zero constraints supply the sharper eta1 case.
The three slope ratios are proved distinct by the actual MDS theorem. -/
theorem actual_shortened_line_pair_eta1 (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 3) (hpq : p ≠ q)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) false) y *
      normalizedResponse inverse q.val.1 q.val.2 (markedPositions e) (fun i => leg (o i) false) y| ≤
      LineOverlap.eta1 := by
  simp_rw [normalizedResponse_eq_slope]
  exact LineOverlap.actual_line_pair_eta1 o (coefficient inverse e p) (coefficient inverse e q)
    (coefficient_nonzero inverse e p) (coefficient_nonzero inverse e q)
    (two_common_zeros_ratios_injective inverse out e p q hpq hcommon)

end AESConcrete.ShortenedLineOverlap
