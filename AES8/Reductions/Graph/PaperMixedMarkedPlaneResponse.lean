import AES8.Estimates.Byte.PaperByteLineBounds
import AESConcrete.MixedMarkedPlaneResponse

/-!
# Exact mixed-plane transport to the printed byte line bound

The existing exact line/plane response identities are reused unchanged.
Only their final analytic mixed-line bound is supplied by the owned printed
second-moment route. The independently fixed orientation on each leg is kept.
The diagonal line/plane cases use the owned cubic provider as well. Other
geometric overlap branches remain separate resources.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperMixedMarkedPlaneResponse
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedPlaneResponse
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.MixedCodeBounds (lineCodeResponse planeCodeResponse)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

/-- The diagonal line case consumes the symbolic absolute-cube provider. -/
theorem actual_line_energy_bound (inverse : Bool) (r z : Fin 16)
    (hline : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y ^ 2) ≤ AESConcrete.ByteLineBounds.a3 := by
  simp_rw [lineCodeResponse_eq_line inverse r z hline marked hm]
  exact AES8.PaperByteLineBounds.actual_line_energy_bound o (fun _ => false) _

/-- The exact Fourier-plane transport preserves the same cubic upper bound. -/
theorem actual_plane_energy_bound (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y ^ 2) ≤ AESConcrete.ByteLineBounds.a3 := by
  simp_rw [actual_plane_response_eq_fourier_leg inverse r z hplane marked hmarked hm]
  exact AES8.PaperByteLineBounds.actual_line_energy_bound o (fun _ => true) _

theorem actual_line_plane_pair_bound (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ AESConcrete.ByteLineBounds.b3 := by
  simp_rw [lineCodeResponse_eq_line inverse r z hline marked hm,
    actual_plane_response_eq_fourier_leg inverse r' z' hplane marked hmarked hm']
  exact AES8.PaperByteLineBounds.actual_mixed_line_pair_bound o _ _

#print axioms actual_line_energy_bound
#print axioms actual_plane_energy_bound
#print axioms actual_line_plane_pair_bound
end AES8.PaperMixedMarkedPlaneResponse
