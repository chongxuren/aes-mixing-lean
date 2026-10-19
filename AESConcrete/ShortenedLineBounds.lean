import AESConcrete.ShortenedLineResponse

/-!
# Bounds for actual normalized shortened-code responses

The geometric response is the product-kernel action on the actual projected
shortened-code indicator, divided by 256. The semantic graph-to-line identity
therefore instantiates the independently established byte line estimates.
No representation or numerical bound is a premise. This remains a line-only
increment; planes, pair-case classification, and the activity frame are separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedLineBounds
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.DampedLineGram (lineResponse)

def normalizedResponse (inverse : Bool) (r z : Fin 16) (marked : Fin 3 → GraphPosition)
    (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) : ℝ :=
  action (coordinateKernel T)
    (codeIndicator (markedGraph (byteDiffusionHom inverse) r z marked)) y / 256

theorem normalizedResponse_eq_line (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    normalizedResponse inverse r z marked T y =
      lineResponse T
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z hshort marked hm) y :=
  byte_normalized_shortened_response inverse r z hshort marked hm T y

theorem actual_shortened_line_pair_bound
    (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool) :
    (4294967296 : ℝ) * |∑ y,
      normalizedResponse inverse r z marked (fun i => ByteLineBounds.leg (o i) (s i)) y *
      normalizedResponse inverse r' z' marked (fun i => ByteLineBounds.leg (o i) (s i)) y| ≤
      ByteLineBounds.a3 := by
  simp_rw [normalizedResponse_eq_line inverse r z hshort marked hm,
    normalizedResponse_eq_line inverse r' z' hshort' marked hm']
  exact ByteLineBounds.actual_line_pair_bound o s _ _

theorem actual_shortened_line_energy_bound
    (inverse : Bool) (r z : Fin 16) (hshort : maskSize r + maskSize z = 3)
    (marked : Fin 3 → GraphPosition) (hm : ∀ i, remaining r z (marked i))
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool) :
    (4294967296 : ℝ) * (∑ y,
      normalizedResponse inverse r z marked (fun i => ByteLineBounds.leg (o i) (s i)) y ^ 2) ≤
      ByteLineBounds.a3 := by
  simp_rw [normalizedResponse_eq_line inverse r z hshort marked hm]
  exact ByteLineBounds.actual_line_energy_bound o s _

/-- Mixed R/RF response pairing for two actual one-parameter shortenings.
Each leg's residual orientation is fixed on the two sides. -/
theorem actual_shortened_mixed_line_pair_bound
    (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y,
      normalizedResponse inverse r z marked (fun i => ByteLineBounds.leg (o i) false) y *
      normalizedResponse inverse r' z' marked (fun i => ByteLineBounds.leg (o i) true) y| ≤
      ByteLineBounds.b3 := by
  simp_rw [normalizedResponse_eq_line inverse r z hshort marked hm,
    normalizedResponse_eq_line inverse r' z' hshort' marked hm']
  exact ByteLineBounds.actual_mixed_line_pair_bound o _ _

end AESConcrete.ShortenedLineBounds
