import AES8.Estimates.Word.PaperWordMoments
import AES8.Math.PaperPatternTransport
import AESConcrete.WordFourierVariants

/-!
# Fixed degree-three HS endpoint for all four whole-word variants

Module role: compose the actual signed three-mark estimate with the exact
whole-word transpose/Fourier correspondence and fixed-pattern transport.
The endpoint covers `R`, `R*`, `F R F`, and `F R* F` with actual AES byte
channels and diffusion directions. Fourier transport retains the explicit
physical coordinate reversal and permutes both residual-position flags.

The bound is strict squared Hilbert--Schmidt energy for each fixed pair of
patterns with total residual degree three: `22 / q`, where `q = 2^32`.
It is neither a degree-aggregated bound nor an operator-norm assertion.
Constructive mathematics only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.PaperWordPatternEnergy
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierVariants (variant baseOrientation baseResidual_eq)
open AESConcrete.WordFourierClosure (residual_fourier reverseKernel)
open AESConcrete.WordFourierDiffusion (wordReverse)
open AESConcrete.MarkedDegreeHilbertSchmidt (patternBlock)
open AESConcrete.HilbertSchmidtEnergy (hs)
open AESConcrete.ActualUnsignedHS (marking marking_card centeredPattern_marking)
open AESPaper.ByteCoordinateTransport (reindexEquiv degreeIndex_reindex)

/-- The actual signed endpoint rewritten as the literal fixed product-projection block. -/
theorem physical_three_mark_strict (left right : Orientation) (inverse : Bool)
    (a b : Fin 4 → Bool) (hthree : (degreeIndex a).val + (degreeIndex b).val = 3) :
    hs (patternBlock 0 (residualMatrix (wordKernel left right inverse) 0) a b) ^ 2 <
      (22 / 4294967296 : ℝ) := by
  have hm := (marking_card a b).trans hthree
  have h := PaperWordMoments.actual_three_mark_strict
    left right inverse (marking a b) hm
  rw [centeredPattern_marking] at h
  change (4294967296 : ℝ) *
    hs (patternBlock 0 (residualMatrix (wordKernel left right inverse) 0) a b) ^ 2 < 22 at h
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4294967296)).2 (by linarith)

/-- Every contextual whole-word variant satisfies the exact strict fixed-pattern cap. -/
theorem variant_three_mark_strict (adjoint fourier : Bool) (a b : Fin 4 → Bool)
    (hthree : (degreeIndex a).val + (degreeIndex b).val = 3) :
    hs (patternBlock 0 (variant adjoint fourier) a b) ^ 2 <
      (22 / 4294967296 : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact physical_three_mark_strict _ _ _ a b hthree
  · rw [if_pos rfl, residual_fourier]
    have hr (K : AES.Word → AES.Word → ℝ) :
        reverseKernel K = reindexKernel (reindexEquiv byteReverse) K := rfl
    rw [hr, PaperPatternTransport.pattern_hs_reindex]
    apply physical_three_mark_strict
    simpa only [degreeIndex_reindex] using hthree

end AES8.PaperWordPatternEnergy
