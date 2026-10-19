import AESConcrete.MixedMarkedPlane
import AESConcrete.MixedMarkedLineOverlap
import AESConcrete.MixedCodeBounds

/-!
# Exact raw mixed-plane Fourier transport

The actual raw plane sum divided by 4096 is transported pointwise to
the actual trace-dual line divided by 256. Only the input legs acquire
Fourier; the original joint output argument is unchanged. The same raw
line convention is identified with the existing line response. This
supplies actual mixed-position diagonal and uniform line/plane endpoints,
without a pair-ratio or signed-aggregate premise. Constructive mathematics
only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPlaneResponse
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedPlane
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.MixedCodeBounds (lineCodeResponse planeCodeResponse)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

theorem normalized_line_eq_code (inverse : Bool) (r z : Fin 16)
    (hline : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    ShortenedLineBounds.normalizedResponse inverse r z marked T y =
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked) T y := by
  unfold ShortenedLineBounds.normalizedResponse
  rw [action_codeIndicator _ _ (markedGraph_injective
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) r z hline marked hm)]
  rfl

theorem lineCodeResponse_eq_line (inverse : Bool) (r z : Fin 16)
    (hline : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked) T y =
      DampedLineGram.lineResponse T
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z hline marked hm) y := by
  rw [← normalized_line_eq_code inverse r z hline marked hm]
  exact ShortenedLineBounds.normalizedResponse_eq_line inverse r z hline marked hm T y

theorem planeCodeResponse_eq_planeResponse (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked) T y =
      PlaneFourierResponse.planeResponse T (plane inverse r z marked) y := by
  unfold planeCodeResponse MixedCodeBounds.codeResponse
    PlaneFourierResponse.planeResponse PlaneFourierResponse.rawResponse
  apply congrArg (fun n : ℝ => n / 4096)
  have h := (planeGraphEquiv inverse r z hplane marked hmarked hm).sum_comp
    (fun c : plane inverse r z marked => coordinateKernel T y c.val)
  simpa only [coordinateKernel, planeGraphEquiv_apply, markedGraph] using h

theorem actual_plane_response_eq_fourier_line (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked) T y =
      DampedLineGram.lineResponse (fun i => kernelCompose (T i) byteFourierMatrix)
        (dualCoordinatePerm inverse r z hplane marked hmarked hm) y := by
  rw [planeCodeResponse_eq_planeResponse inverse r z hplane marked hmarked hm]
  exact PlaneFourierResponse.plane_response_eq_fourier_line T (plane inverse r z marked)
    (plane_card inverse r z hplane marked hmarked hm)
    (dualCoordinatePerm inverse r z hplane marked hmarked hm)
    (dualParam inverse r z hplane marked hmarked hm)
    (dualParam_coordinate inverse r z hplane marked hmarked hm) y

theorem actual_plane_response_eq_fourier_leg (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (o : Fin 3 → Orientation) (y : Fin 3 → Byte) :
    planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y =
      DampedLineGram.lineResponse (fun i => leg (o i) true)
        (dualCoordinatePerm inverse r z hplane marked hmarked hm) y :=
  actual_plane_response_eq_fourier_line inverse r z hplane marked hmarked hm _ y

theorem actual_line_energy_bound (inverse : Bool) (r z : Fin 16)
    (hline : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y ^ 2) ≤ ByteLineBounds.a3 := by
  simp_rw [lineCodeResponse_eq_line inverse r z hline marked hm]
  exact ByteLineBounds.actual_line_energy_bound o (fun _ => false) _

theorem actual_plane_energy_bound (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y ^ 2) ≤ ByteLineBounds.a3 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse r z hplane marked hmarked hm]
  exact ByteLineBounds.actual_line_energy_bound o (fun _ => true) _

theorem actual_line_plane_pair_bound (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ ByteLineBounds.b3 := by
  simp_rw [lineCodeResponse_eq_line inverse r z hline marked hm,
    actual_plane_response_eq_fourier_leg inverse r' z' hplane marked hmarked hm']
  exact ByteLineBounds.actual_mixed_line_pair_bound o _ _

end AESConcrete.MixedMarkedPlaneResponse
