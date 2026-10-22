import AES8.Estimates.Word.PaperWordMoments
import AESConcrete.WordFourierVariants

/-!
# Actual word-variant traces on the printed degree-HS route

Module role: transport the owned physical word trace to the four literal
transpose/Fourier variants. The exact adjoint, whole-word Fourier and
coordinate-reversal identities are reused; the historical trace bounds are
not premises. Public constants and counting normalization stay unchanged.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperWordTraceVariants
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierVariants (variant baseResidual_eq)
open AESConcrete.WordFourierClosure (residual_fourier)
open AESConcrete.WordFourierBounds (reverse_trace)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The physical trace provider is the owned complete degree-HS assembly. -/
theorem residual_trace_lt (left right : Orientation) (inverse : Bool) :
    (∑ y, ∑ x, residualMatrix (wordKernel left right inverse) 0 y x ^ 2) <
      (4251 / 4294967296 : ℝ) :=
  PaperWordMoments.actual_trace_bound left right inverse

/-- Exact adjoint/Fourier transports preserve the same total square sum. -/
theorem variant_trace_lt (adjoint fourier : Bool) :
    (∑ y, ∑ x, variant adjoint fourier y x ^ 2) <
      (4251 / 4294967296 : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact residual_trace_lt _ _ _
  · simp only [if_true]
    rw [residual_fourier, reverse_trace]
    exact residual_trace_lt _ _ _

#print axioms residual_trace_lt
#print axioms variant_trace_lt
end AES8.PaperWordTraceVariants
