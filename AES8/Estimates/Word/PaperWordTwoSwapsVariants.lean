import AES8.Estimates.Word.PaperWordTwoSwaps
import AESConcrete.WordFourierVariants

/-! Public word Gram-moment resources following the paper's literal two-swap
proof. The Fourier and adjoint transports preserve the same scalar moment;
the historical per-summand minimum bound is not used as a premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperWordTwoSwapsVariants
open AESMixing AESConcrete
open WordFourierVariants WordFourierBounds WordFourierCore
open WordOrientationClosure (wordKernel)
open WordFourierClosure (residual_fourier)

theorem residual_gram_moment_lt (left right : ByteOrientations.Orientation)
    (inverse : Bool) :
    (∑ x, ∑ z, (∑ y,
      residualMatrix (wordKernel left right inverse) 0 y x *
      residualMatrix (wordKernel left right inverse) 0 y z)^2) <
      (300 / 4294967296 : ℝ)^2 := by
  have h := PaperWordTwoSwaps.actual_gram_moment_lt left right inverse
  change (4294967296 : ℝ)^2 *
    (∑ x, ∑ z, (∑ y,
      residualMatrix (wordKernel left right inverse) 0 y x *
      residualMatrix (wordKernel left right inverse) 0 y z)^2) < 89870 at h
  nlinarith

theorem variant_gram_moment_lt (adjoint fourier : Bool) :
    (∑ x, ∑ z, (∑ y, variant adjoint fourier y x * variant adjoint fourier y z)^2) <
      (300 / 4294967296 : ℝ)^2 := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact residual_gram_moment_lt _ _ _
  · simp only [if_true]
    rw [residual_fourier, reverse_gram_moment]
    exact residual_gram_moment_lt _ _ _

end AES8.PaperWordTwoSwapsVariants
