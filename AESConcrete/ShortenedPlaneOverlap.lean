import AESConcrete.ShortenedPlaneGeometry
import AESConcrete.ShortenedPlaneResponse
import AESConcrete.FourierLineOverlap
import AESConcrete.ShortenedLineOverlap

/-!
# Actual shortened-plane overlap estimates

The actual plane response is rewritten in the original output space as an
input-Fourier line response. Its field coefficients and ratio separation
are derived from the actual trace annihilator and physical MDS geometry.
The same-flag Gram transport then supplies the exact eta1 and eta2 bounds.
No slope table, assumed code separation, or residual/Fourier commutation
enters the wrappers. Constructive scope; full word assembly remains open.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ShortenedPlaneOverlap
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineBounds
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ShortenedPlane
open AESConcrete.ShortenedPlaneLinearity
open AESConcrete.ShortenedPlaneGeometry
open AESConcrete.ShortenedPlaneResponse
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)

theorem dualCoordinatePerm_eq_slope (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) :
    dualCoordinatePerm inverse out hout e p =
      LineOverlap.slopeEquiv (dualCoefficient inverse out hout e p)
        (dualCoefficient_ne_zero inverse out hout e p) := by
  funext i
  exact dualCoordinatePerm_eq_mulLeft inverse out hout e p i

/-- Every pair of distinct actual plane shortenings obeys eta2. -/
theorem actual_shortened_plane_pair_eta2 (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 2) (hpq : p ≠ q) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedPlaneResponse inverse e p (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y| ≤
      LineOverlap.eta2 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse out hout e,
    dualCoordinatePerm_eq_slope inverse out hout e]
  exact FourierLineOverlap.actual_line_pair_eta2 o (fun _ => true)
    (dualCoefficient inverse out hout e p) (dualCoefficient inverse out hout e q)
    (dualCoefficient_ne_zero inverse out hout e p) (dualCoefficient_ne_zero inverse out hout e q)
    (distinct_plane_ratios_nonconstant inverse out hout e p q hpq)

/-- One common physical zero constraint supplies the sharper eta1 estimate. -/
theorem actual_shortened_plane_pair_eta1 (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 2) (hpq : p ≠ q)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedPlaneResponse inverse e p (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y| ≤
      LineOverlap.eta1 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse out hout e,
    dualCoordinatePerm_eq_slope inverse out hout e]
  exact FourierLineOverlap.actual_line_pair_eta1 o (fun _ => true)
    (dualCoefficient inverse out hout e p) (dualCoefficient inverse out hout e q)
    (dualCoefficient_ne_zero inverse out hout e p) (dualCoefficient_ne_zero inverse out hout e q)
    (one_common_zero_ratios_injective inverse out hout e p q hpq hcommon)

/-- The actual line estimates now allow arbitrary shared per-leg Fourier flags. -/
theorem actual_shortened_line_same_flag_eta2 (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 3) (hpq : p ≠ q)
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) (s i)) y *
      normalizedResponse inverse q.val.1 q.val.2 (markedPositions e) (fun i => leg (o i) (s i)) y| ≤
      LineOverlap.eta2 := by
  simp_rw [ShortenedLineOverlap.normalizedResponse_eq_slope]
  exact FourierLineOverlap.actual_line_pair_eta2 o s _ _
    (ShortenedLineGeometry.coefficient_nonzero inverse e p)
    (ShortenedLineGeometry.coefficient_nonzero inverse e q)
    (ShortenedLineGeometry.distinct_choices_ratios_nonconstant inverse out hout e p q hpq)

theorem actual_shortened_line_same_flag_eta1 (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 3) (hpq : p ≠ q)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2)
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedResponse inverse p.val.1 p.val.2 (markedPositions e) (fun i => leg (o i) (s i)) y *
      normalizedResponse inverse q.val.1 q.val.2 (markedPositions e) (fun i => leg (o i) (s i)) y| ≤
      LineOverlap.eta1 := by
  simp_rw [ShortenedLineOverlap.normalizedResponse_eq_slope]
  exact FourierLineOverlap.actual_line_pair_eta1 o s _ _
    (ShortenedLineGeometry.coefficient_nonzero inverse e p)
    (ShortenedLineGeometry.coefficient_nonzero inverse e q)
    (ShortenedLineGeometry.two_common_zeros_ratios_injective inverse out e p q hpq hcommon)

end AESConcrete.ShortenedPlaneOverlap
