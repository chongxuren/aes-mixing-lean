import AESConcrete.ShortenedPlane
import AESConcrete.PlaneFourierResponse
import AESConcrete.ShortenedLineBounds

/-!
# Fourier-line responses of actual shortened AES planes

The actual two-zero projected-code response, divided by 4096, is exactly
the three-leg Fourier-input response on the actual dual line. Its output
argument is unchanged. The subgroup, cardinality, dual coordinate equivalence,
and three coordinate permutations are all derived in ShortenedPlane.
Constructive scope only; the remaining pair classes and word assembly remain
separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedPlaneResponse
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ShortenedPlane
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.DampedLineGram (lineResponse)

def normalizedPlaneResponse (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) : ℝ :=
  action (coordinateKernel T)
    (codeIndicator (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e))) y / 4096

-- Unfolding the actual byte graph/range predicates crosses the concrete
-- field instances; the higher elaboration depth changes no proof mechanism.
set_option maxRecDepth 65536 in
theorem normalizedPlaneResponse_eq_plane (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedPlaneResponse inverse e p T y =
      PlaneFourierResponse.planeResponse T (plane inverse e p) y := by
  unfold normalizedPlaneResponse
  have hind : codeIndicator
      (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)) =
      PlaneFourierResponse.subgroupIndicator (plane inverse e p) := by
    classical
    funext v
    have he : (∃ u : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2,
        markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) u = v) ↔
        v ∈ plane inverse e p := by
      constructor
      · rintro ⟨u, hu⟩
        change ∃ x : graphSubgroup inverse p.val.1 p.val.2,
          projectionHom inverse p.val.1 p.val.2 e x = v
        exact ⟨⟨u.val, u.property⟩, hu⟩
      · intro hv
        change ∃ x : graphSubgroup inverse p.val.1 p.val.2,
          projectionHom inverse p.val.1 p.val.2 e x = v at hv
        obtain ⟨u, hu⟩ := hv
        exact ⟨⟨u.val, u.property⟩, hu⟩
    unfold codeIndicator PlaneFourierResponse.subgroupIndicator
    simp only [he]
  rw [hind, PlaneFourierResponse.action_subgroupIndicator]
  rfl

/-- Exact pointwise duality for the actual two-zero shortening. The
product response stays in its original output space. -/
theorem actual_plane_response_eq_fourier_line (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedPlaneResponse inverse e p T y =
      lineResponse (fun i => kernelCompose (T i) byteFourierMatrix)
        (dualCoordinatePerm inverse out hout e p) y := by
  rw [normalizedPlaneResponse_eq_plane inverse out hout e p]
  exact PlaneFourierResponse.plane_response_eq_fourier_line T (plane inverse e p)
    (plane_card inverse out hout e p) (dualCoordinatePerm inverse out hout e p)
    (dualParam inverse out hout e p) (dualParam_coordinate inverse out hout e p) y

theorem actual_plane_response_eq_fourier_leg (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (o : Fin 3 → Orientation) (y : Fin 3 → Byte) :
    normalizedPlaneResponse inverse e p (fun i => leg (o i) false) y =
      lineResponse (fun i => leg (o i) true) (dualCoordinatePerm inverse out hout e p) y := by
  exact actual_plane_response_eq_fourier_line inverse out hout e p _ y

theorem actual_shortened_plane_energy_bound (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      normalizedPlaneResponse inverse e p (fun i => leg (o i) false) y ^ 2) ≤ ByteLineBounds.a3 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse out hout e p]
  exact ByteLineBounds.actual_line_energy_bound o (fun _ => true) _

theorem actual_shortened_plane_pair_bound (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 2) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      normalizedPlaneResponse inverse e p (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y| ≤ ByteLineBounds.a3 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse out hout e p,
    actual_plane_response_eq_fourier_leg inverse out hout e q]
  exact ByteLineBounds.actual_line_pair_bound o (fun _ => true) _ _

/-- The actual line/plane pair is an ordinary/Fourier-input line pair.
This uniform b3 bound does not require an activity-intersection premise. -/
theorem actual_shortened_line_plane_pair_bound (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (q : ShorteningChoice out 2) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      ShortenedLineBounds.normalizedResponse inverse p.val.1 p.val.2 (markedPositions e)
        (fun i => leg (o i) false) y *
      normalizedPlaneResponse inverse e q (fun i => leg (o i) false) y| ≤ ByteLineBounds.b3 := by
  simp_rw [ShortenedLineBounds.normalizedResponse_eq_line inverse p.val.1 p.val.2 p.property.2
    (markedPositions e) (ShortenedLineGeometry.marked_remaining e p),
    actual_plane_response_eq_fourier_leg inverse out hout e q]
  exact ByteLineBounds.actual_mixed_line_pair_bound o _ _

end AESConcrete.ShortenedPlaneResponse
