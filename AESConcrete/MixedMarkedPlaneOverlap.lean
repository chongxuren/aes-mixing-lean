import AESConcrete.MixedMarkedPlaneGeometry
import AESConcrete.MixedMarkedPlaneResponse
import AESConcrete.FourierLineOverlap

/-!
# Actual raw same-type overlap endpoints for mixed physical triples

The actual plane response acquires Fourier only on its input legs. Its
trace-dual coefficients and ratio separation are supplied by the actual
mixed-coordinate geometry. Existing analytic estimates give eta1/eta2 in
the original joint output space. Raw line wrappers use the same /256
convention as the contraction bridge. No signed aggregate or final bound
is assumed. Constructive mathematics only; no attacks or frozen edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPlaneOverlap
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedPlane
open AESConcrete.MixedMarkedPlaneLinearity
open AESConcrete.MixedMarkedPlaneGeometry
open AESConcrete.MixedMarkedPlaneResponse
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.MixedCodeBounds (lineCodeResponse planeCodeResponse)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

theorem dualCoordinatePerm_eq_slope (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    dualCoordinatePerm inverse r z hplane marked hmarked hm =
      LineOverlap.slopeEquiv (dualCoefficient inverse r z hplane marked hmarked hm)
        (dualCoefficient_ne_zero inverse r z hplane marked hmarked hm) := by
  funext i
  exact dualCoordinatePerm_eq_mulLeft inverse r z hplane marked hmarked hm i

theorem actual_plane_pair_eta2 (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') ≤ 1)
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ LineOverlap.eta2 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse r z hplane marked hmarked hm,
    actual_plane_response_eq_fourier_leg inverse r' z' hplane' marked hmarked hm',
    dualCoordinatePerm_eq_slope inverse r z hplane marked hmarked hm,
    dualCoordinatePerm_eq_slope inverse r' z' hplane' marked hmarked hm']
  exact FourierLineOverlap.actual_line_pair_eta2 o (fun _ => true) _ _
    (dualCoefficient_ne_zero inverse r z hplane marked hmarked hm)
    (dualCoefficient_ne_zero inverse r' z' hplane' marked hmarked hm')
    (plane_ratios_nonconstant inverse r z r' z' hplane hplane' marked hmarked hm hm' hcommon)

theorem actual_plane_pair_eta1 (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 1)
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ LineOverlap.eta1 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse r z hplane marked hmarked hm,
    actual_plane_response_eq_fourier_leg inverse r' z' hplane' marked hmarked hm',
    dualCoordinatePerm_eq_slope inverse r z hplane marked hmarked hm,
    dualCoordinatePerm_eq_slope inverse r' z' hplane' marked hmarked hm']
  exact FourierLineOverlap.actual_line_pair_eta1 o (fun _ => true) _ _
    (dualCoefficient_ne_zero inverse r z hplane marked hmarked hm)
    (dualCoefficient_ne_zero inverse r' z' hplane' marked hmarked hm')
    (plane_ratios_injective inverse r z r' z' hplane hplane' marked hmarked hm hm' hcommon)

theorem actual_line_pair_eta2 (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hline' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 1 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z'))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ LineOverlap.eta2 := by
  simp_rw [← normalized_line_eq_code inverse r z hline marked hm,
    ← normalized_line_eq_code inverse r' z' hline' marked hm']
  exact MixedMarkedLineOverlap.actual_line_pair_eta2 inverse r z r' z' hline hline'
    marked hmarked hm hm' hcommon hunion o (fun _ => false)

theorem actual_line_pair_eta1 (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hline' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 2 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z'))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ LineOverlap.eta1 := by
  simp_rw [← normalized_line_eq_code inverse r z hline marked hm,
    ← normalized_line_eq_code inverse r' z' hline' marked hm']
  exact MixedMarkedLineOverlap.actual_line_pair_eta1 inverse r z r' z' hline hline'
    marked hmarked hm hm' hcommon hunion o (fun _ => false)

end AESConcrete.MixedMarkedPlaneOverlap
