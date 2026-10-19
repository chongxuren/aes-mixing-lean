import AESConcrete.MixedMarkedPairGeometry
import AESConcrete.MixedCodeBounds
import AESConcrete.ContainmentCodeBounds

/-!
# Actual mixed physical line/plane overlap estimates

The actual raw shortened graphs supply every geometric premise of the
independent-leg transverse and signed containment estimates. The line /256
and plane /4096 conventions are explicit. Contracted-frame reindexing,
plane-dual line geometry and the full signed aggregate remain separate.
Constructive mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPairBounds
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedMixedGeometry (markedGraph_zero)
open AESConcrete.MixedMarkedPairGeometry
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.MixedCodeBounds (lineCodeResponse planeCodeResponse)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

theorem actual_transverse_bound (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 1)
    (o : Fin 3 → Orientation) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y| ≤ MixedCodeBounds.f3 := by
  apply MixedCodeBounds.actual_transverse_bound o _ _
    (zeroGraph _ r z) (zeroGraph _ r' z')
    (markedGraph_zero _ _ _ _) (markedGraph_zero _ _ _ _)
  exact differenceMap_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z r' z' hline hplane marked hmarked hm (by omega)
    (by rw [mixed_union_four r z r' z' hline hplane hcommon])

/-- The signed midpoint and error are derived for every mixed physical
triple; no actual shift, fiber count or nonzero-coordinate premise remains. -/
theorem actual_containment_bound (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 2)
    (o : Fin 3 → Orientation) :
    |(4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
        (fun i => leg (o i) false) y *
      planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
        (fun i => leg (o i) false) y) - ContainmentCodeBounds.z3| ≤ ContainmentCodeBounds.h3 := by
  let hcontains := plane_zeros_in_line r z r' z' hline hplane hcommon
  have hc : Fintype.card (ShortenedGraph (byteDiffusionHom inverse) r z) = 256 := by
    rw [mds_graph_zero_count _ (byteDiffusionHom_zeroMDS inverse), hline]
    norm_num [BinaryWord.card]
  have hd : Fintype.card (ShortenedGraph (byteDiffusionHom inverse) r' z') = 65536 := by
    rw [mds_graph_zero_count _ (byteDiffusionHom_zeroMDS inverse), hplane]
    norm_num [BinaryWord.card]
  apply ContainmentCodeBounds.actual_containment_bound o _ _
    (zeroGraph _ r z) (zeroGraph _ r' z')
    (markedGraph_zero _ _ _ _) (markedGraph_zero _ _ _ _) hc hd
    (nonzero_line_marked_coordinate _ (byteDiffusionHom_zeroMDS inverse) r z hline marked hm)
    (fun i => by
      simpa only [BinaryWord.card, Nat.reducePow] using
        marked_zero_fiber_card _ (byteDiffusionHom_zeroMDS inverse) r' z' hplane marked hmarked hm' i)
    (two_marked_zeros_force_zero _ (byteDiffusionHom_zeroMDS inverse) r' z' hplane marked hmarked hm')
    (shift (byteDiffusionHom inverse) r z r' z' hcontains)
  intro x w i
  exact congrFun (marked_shift_difference (byteDiffusionHom inverse) r z r' z'
    marked hcontains x w) i

theorem actual_containment_interval (inverse : Bool) (r z r' z' : Fin 16)
    (hline : maskSize r + maskSize z = 3) (hplane : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 2)
    (o : Fin 3 → Orientation) :
    ContainmentCodeBounds.z3-ContainmentCodeBounds.h3 ≤
        (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
          lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
            (fun i => leg (o i) false) y *
          planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
            (fun i => leg (o i) false) y) ∧
      (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
          lineCodeResponse (markedGraph (byteDiffusionHom inverse) r z marked)
            (fun i => leg (o i) false) y *
          planeCodeResponse (markedGraph (byteDiffusionHom inverse) r' z' marked)
            (fun i => leg (o i) false) y) ≤
        ContainmentCodeBounds.z3+ContainmentCodeBounds.h3 := by
  have h := abs_le.mp
    (actual_containment_bound inverse r z r' z' hline hplane marked hmarked hm hm' hcommon o)
  constructor <;> linarith [h.1,h.2]

end AESConcrete.MixedMarkedPairBounds
