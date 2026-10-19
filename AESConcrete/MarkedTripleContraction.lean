import AESConcrete.MarkedBlockScale
import AESConcrete.ActualMarkedCodeMoment
import AESConcrete.MixedCodeBounds

/-!
# Exact physical marked-triple contraction normalization

A coordinate equivalence only reindexes the three marked physical legs.
Their input/output tags and actual adjoint orientations are retained.
The raw shortened-source response is divided by 256 for a line and by
4096 for a plane, as derived from the actual uniform frame count. Joint
output pairings are preserved exactly by a displayed finite bijection.
No overlap endpoint or signed aggregate is assumed. Constructive
mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedTripleContraction
open AESMixing AESMixing.AES
open AESConcrete.MarkedBlockVectorization
open AESConcrete.MarkedBlockShortening
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ActualMarkedCodeMoment (markedOrientation actual_markedLeg marked_remaining)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

def triplePositions (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m) :
    Fin 3 → GraphPosition := fun i => (e i).val

theorem triplePositions_injective (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m) :
    Function.Injective (triplePositions m e) :=
  Subtype.val_injective.comp e.injective

theorem triplePositions_remaining (m : GraphPosition → Bool) (s : Activity m → Bool)
    (e : Fin 3 ≃ Marked m) (i : Fin 3) :
    remaining (outputZeros m s) (inputZeros m s) (triplePositions m e i) :=
  marked_remaining m s (e i)

def outputEquiv (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m) :
    (Marked m → Byte) ≃ (Fin 3 → Byte) :=
  Equiv.arrowCongr e.symm (Equiv.refl Byte)

theorem outputEquiv_apply (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m)
    (y : Marked m → Byte) (i : Fin 3) : outputEquiv m e y i = y (e i) := rfl

theorem outputEquiv_symm_apply (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m)
    (y : Fin 3 → Byte) (p : Marked m) : (outputEquiv m e).symm y p = y (e.symm p) := rfl

/-- Reindex only the product of marked legs; the actual source subtype
and each physical graph coordinate are unchanged. -/
theorem rawResponse_reindex (L : (Fin 4 → Byte) →+ (Fin 4 → Byte))
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (T : Marked m → Byte → Byte → ℝ) (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    rawResponse L m s T y =
      MixedCodeBounds.codeResponse
        (markedGraph L (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => T (e i)) (outputEquiv m e y) := by
  unfold rawResponse MixedCodeBounds.codeResponse
  apply Finset.sum_congr rfl
  intro c _
  exact (e.prod_comp (fun p : Marked m =>
    T p (y p) (sourceCoordinates L m s c p))).symm

theorem contractedResponse_reindex (L : (Fin 4 → Byte) →+ (Fin 4 → Byte))
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (T : Marked m → Byte → Byte → ℝ) (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    contractedResponse m T (graphCoordinate L) s y =
      MixedCodeBounds.codeResponse
        (markedGraph L (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => T (e i)) (outputEquiv m e y) / (16 : ℝ)^uniformCount s := by
  rw [contractedResponse_shortened (by norm_num [BinaryWord.card]),
    rawResponse_reindex L m s T e y]

theorem line_uniformCount (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 3) :
    uniformCount s = 2 := by
  have h := MarkedBlockScale.count_balance m s
  omega

theorem plane_uniformCount (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 2) :
    uniformCount s = 3 := by
  have h := MarkedBlockScale.count_balance m s
  omega

theorem contractedResponse_eq_line (L : (Fin 4 → Byte) →+ (Fin 4 → Byte))
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 3)
    (T : Marked m → Byte → Byte → ℝ) (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    contractedResponse m T (graphCoordinate L) s y =
      MixedCodeBounds.lineCodeResponse
        (markedGraph L (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => T (e i)) (outputEquiv m e y) := by
  rw [contractedResponse_reindex L m s T e y, line_uniformCount m hlen s hz]
  norm_num [MixedCodeBounds.lineCodeResponse]

theorem contractedResponse_eq_plane (L : (Fin 4 → Byte) →+ (Fin 4 → Byte))
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 2)
    (T : Marked m → Byte → Byte → ℝ) (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    contractedResponse m T (graphCoordinate L) s y =
      MixedCodeBounds.planeCodeResponse
        (markedGraph L (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => T (e i)) (outputEquiv m e y) := by
  rw [contractedResponse_reindex L m s T e y, plane_uniformCount m hlen s hz]
  norm_num [MixedCodeBounds.planeCodeResponse]

def tripleOrientation (left right : Orientation) (m : GraphPosition → Bool)
    (e : Fin 3 ≃ Marked m) : Fin 3 → Orientation :=
  fun i => markedOrientation left right m (e i)

/-- In particular, physical input legs keep the adjoint of right. -/
theorem actualLeg_reindex (left right : Orientation) (m : GraphPosition → Bool)
    (e : Fin 3 ≃ Marked m) :
    (fun i => markedLeg (channel left) (channel right) m (e i)) =
      fun i => ByteLineBounds.leg (tripleOrientation left right m e i) false := by
  rw [actual_markedLeg]
  rfl

theorem actual_contractedResponse_eq_line (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 3)
    (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
        (graphCoordinate (byteDiffusionHom inverse)) s y =
      MixedCodeBounds.lineCodeResponse
        (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => ByteLineBounds.leg (tripleOrientation left right m e i) false) (outputEquiv m e y) := by
  rw [contractedResponse_eq_line _ m hlen s hz _ e y, actualLeg_reindex]

theorem actual_contractedResponse_eq_plane (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3)
    (s : Activity m → Bool) (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) = 2)
    (e : Fin 3 ≃ Marked m) (y : Marked m → Byte) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
        (graphCoordinate (byteDiffusionHom inverse)) s y =
      MixedCodeBounds.planeCodeResponse
        (markedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) (triplePositions m e))
        (fun i => ByteLineBounds.leg (tripleOrientation left right m e i) false) (outputEquiv m e y) := by
  rw [contractedResponse_eq_plane _ m hlen s hz _ e y, actualLeg_reindex]

/-- The joint output pairing is invariant under this actual coordinate
bijection. No input kernel or Fourier operation is moved to the output. -/
theorem pair_sum_reindex (m : GraphPosition → Bool) (e : Fin 3 ≃ Marked m)
    (F G : (Marked m → Byte) → ℝ) :
    (∑ y : Marked m → Byte, F y * G y) =
      ∑ y : Fin 3 → Byte, F ((outputEquiv m e).symm y) * G ((outputEquiv m e).symm y) :=
  ((outputEquiv m e).symm.sum_comp (fun y => F y * G y)).symm

end AESConcrete.MarkedTripleContraction
