import AES8.Estimates.Word.PaperDegreeThreeParityEndpoint
import AES8.Reductions.Support.PaperDegreeReverse
import AES8.Math.PaperKernelReindex
import AESConcrete.WordFourierVariants

/-!
# Parity-derived strict blocks for the four physical word variants

The numerical endpoint is imported from the uniform parity-margin proof.
Both flags denote actual transpose and simultaneous Fourier operations.
Fourier identification retains the physical coordinate reversal, whose
commutation with the byte-degree projections is independently proved.
No arbitrary-unitary degree invariance is assumed.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParityVariants
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierVariants (variant baseResidual_eq)
open AESConcrete.WordFourierClosure (residual_fourier reverseKernel)
open AESConcrete.WordFourierDiffusion (wordReverse)
open AESConcrete.DegreeHilbertSchmidt (block)
set_option autoImplicit false
set_option maxRecDepth 100000

theorem physical_block_norm_lt (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (hij : (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)) :
    ‖kernelOperator (block 0 (residualMatrix (wordKernel left right inverse) 0) i j)‖ <
      (33 / (10 * 65536) : ℝ) := by
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact PaperDegreeThreeParityEndpoint.forward_operator_norm_lt left right inverse
  · exact PaperDegreeThreeParityEndpoint.reverse_operator_norm_lt left right inverse

theorem reverse_norm (K : AES.Word → AES.Word → ℝ) :
    ‖kernelOperator (reindexKernel wordReverse K)‖ = ‖kernelOperator K‖ :=
  PaperKernelReindex.kernelOperator_reindex wordReverse wordReverse K

/-- Every contextual matrix has the exact strict endpoint, including its
actual Fourier-induced byte orientations and inverse diffusion. -/
theorem variant_block_norm_lt (adjoint fourier : Bool) (i j : Fin 5)
    (hij : (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)) :
    ‖kernelOperator (block 0 (variant adjoint fourier) i j)‖ <
      (33 / (10 * 65536) : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact physical_block_norm_lt _ _ _ i j hij
  · rw [if_pos rfl, residual_fourier]
    have hr (K : AES.Word → AES.Word → ℝ) :
        reverseKernel K = reindexKernel wordReverse K := rfl
    rw [hr, PaperDegreeReverse.block_reverse, reverse_norm]
    exact physical_block_norm_lt _ _ _ i j hij

theorem variant_forward_operator_norm_lt (adjoint fourier : Bool) :
    ‖kernelOperator (block 0 (variant adjoint fourier) 3 0)‖ <
      (33 / (10 * 65536) : ℝ) :=
  variant_block_norm_lt adjoint fourier 3 0 (Or.inl ⟨rfl, rfl⟩)

theorem variant_reverse_operator_norm_lt (adjoint fourier : Bool) :
    ‖kernelOperator (block 0 (variant adjoint fourier) 0 3)‖ <
      (33 / (10 * 65536) : ℝ) :=
  variant_block_norm_lt adjoint fourier 0 3 (Or.inr ⟨rfl, rfl⟩)

/-- `localres:degree-three` at the frozen paper's literal normalization. -/
theorem paper_degree_three (adjoint fourier : Bool) :
    Real.sqrt ((2 : ℝ)^32) *
        ‖kernelOperator (block 0 (variant adjoint fourier) 3 0)‖ < 33 / 10 ∧
    Real.sqrt ((2 : ℝ)^32) *
        ‖kernelOperator (block 0 (variant adjoint fourier) 0 3)‖ < 33 / 10 := by
  have hs : Real.sqrt ((2 : ℝ)^32) = 65536 := by
    rw [show (2 : ℝ)^32 = 65536^2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
  rw [hs]
  have hf := variant_forward_operator_norm_lt adjoint fourier
  have hr := variant_reverse_operator_norm_lt adjoint fourier
  constructor <;> nlinarith

end AES8.PaperDegreeThreeParityVariants
