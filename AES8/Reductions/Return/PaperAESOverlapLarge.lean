import AES8.Reductions.Return.PaperAESOverlapResources
import AES8.Reductions.Return.PaperWholeGraphReturn
import AES8.Reductions.Return.PaperReturnDimensions
import AES8.Math.PaperPhysicalOverlap

/-!
# The AES information-set overlap with its literal fiber normalization

Frozen paper f902bb94, normalization interface for `eq:aesasm-overlap-large`.
This leaf defines the collision-product coefficient and literal complex
normalized overlap, and proves the real compressed-kernel identity.
The large-overlap norm bound and its complexification remain separate
obligations. Incidence factors and the physical whole-state join belong
to other leaves. No target bound is assumed or asserted here.
Constructive proof checking only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapLarge
open AESMixing AESConcrete PaperMDSGram PaperMDSOverlap PaperPhysicalOverlap
open PaperFiberKernel PaperKernelBounds PaperAESOverlapResources

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {KL KR M : Type*} [Fintype KL] [DecidableEq KL]
  [Fintype KR] [DecidableEq KR] [Fintype M] [DecidableEq M]

/-- The normalized collision product, before the paper's half-power rewrite. -/
def coefficient (m s t a b : ℕ) : ℝ :=
  nu ^ (s + t - m) * Real.sqrt
    (delta ^ (m - s - a) * total ^ a *
      (delta ^ (m - t - b) * total ^ b) / (q : ℝ) ^ (a + b))

theorem coefficient_nonneg (m s t a b : ℕ) : 0 ≤ coefficient m s t a b :=
  mul_nonneg (pow_nonneg nu_nonneg _) (Real.sqrt_nonneg _)


/-- Direct normalized matrix, with no information-coordinate choices. -/
def overlap (CL : AddSubgroup (KL → AES.Word)) (CR : AddSubgroup (KR → AES.Word))
    (s t : ℕ) (offL : KL → AES.Word) (offR : KR → AES.Word)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR) (adjoint eL eR : Bool) :
    EuclideanSpace ℂ (OutsideLabel CR offR outsideR) →L[ℂ]
      EuclideanSpace ℂ (OutsideLabel CL offL outsideL) :=
  (fiberLift (𝕜 := ℂ) (outsideProjection CL offL outsideL)
    (q ^ (s - min s outsideL.card))).adjoint.comp
      ((kernelOperator (fun y x =>
        (physicalMiddleKernel CL CR offL offR middleL middleR
          (fun _ => PaperWordMixedGram.mixed adjoint eL eR) y x : ℂ))).comp
        (fiberLift (𝕜 := ℂ) (outsideProjection CR offR outsideR)
          (q ^ (t - min t outsideR.card))))


/-- The real function-space representation has precisely the same normalizer. -/
theorem physicalOverlap_eq_compressed_action
    (CL : AddSubgroup (KL → AES.Word)) (CR : AddSubgroup (KR → AES.Word))
    (s t : ℕ) (offL : KL → AES.Word) (offR : KR → AES.Word)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (T : M → AES.Word → AES.Word → ℝ)
    (f : OutsideLabel CR offR outsideR → ℝ) :
    physicalOverlap CL CR s t offL offR middleL middleR outsideL outsideR T f =
      action (compressedKernel (outsideProjection CL offL outsideL)
        (outsideProjection CR offR outsideR)
        (q ^ (s - min s outsideL.card)) (q ^ (t - min t outsideR.card))
        (physicalMiddleKernel CL CR offL offR middleL middleR T)) f := by
  simp only [physicalOverlap, WordFourierCore.word_card, q]
  funext x
  symm
  exact compressedKernel_action _ _ _ _ _ f x



end AES8.PaperAESOverlapLarge
