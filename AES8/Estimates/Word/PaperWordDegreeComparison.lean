import AES8.Reductions.Support.PaperDegreeReverse
import AES8.Estimates.Word.PaperDampedDegreeBounds
import AESConcrete.WordFourierVariants
import AES8.Math.PaperRealComplexEnergy

/-! The literal paper's 5-by-5 comparison for actual residual degree blocks.
The shared numerical leaf owns the exact table. The shared block theorem
uses the literal degree-three parity and degree-two slope routes. Physical
Fourier variants use explicit reversal. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperWordDegreeComparison
open AESMixing AESConcrete.WordOrientationClosure AESConcrete.DegreeHilbertSchmidt
open AESConcrete.WordFourierDiffusion AESConcrete.WordFourierVariants
open PaperKernelBounds
set_option autoImplicit false
set_option maxRecDepth 100000

theorem residual_block_energy (left right : AESConcrete.ByteOrientations.Orientation)
    (inverse : Bool) (i j : Fin 5) (f : AES.Word → ℝ) :
    (∑ y, action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f y^2) ≤
      (comparison i j/65536)^2 * ∑ x, f x^2 :=
  PaperDampedDegreeBounds.residual_block_table_energy left right inverse i j f

theorem variant_block_energy (adjoint fourier : Bool) (i j : Fin 5)
    (f : AES.Word → ℝ) :
    (∑ y, action (block 0 (variant adjoint fourier) i j) f y^2) ≤
      (comparison i j/65536)^2 * ∑ x, f x^2 := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact residual_block_energy _ _ _ i j f
  · rw [AESConcrete.WordFourierClosure.residual_fourier]
    change (∑ y, action (block 0 (reindexKernel wordReverse _) i j) f y^2) ≤ _
    rw [PaperDegreeReverse.block_reverse]
    exact reindexKernel_energy wordReverse _ _ (residual_block_energy _ _ _ i j) f

theorem variant_block_complex_energy (adjoint fourier : Bool) (i j : Fin 5)
    (f : AES.Word → ℂ) :
    (∑ y, ‖kernelAction (fun y x => (block 0 (variant adjoint fourier) i j y x : ℂ)) f y‖^2) ≤
      (comparison i j/65536)^2 * ∑ x, ‖f x‖^2 :=
  PaperRealComplexEnergy.complex_energy_of_real _ _ (variant_block_energy adjoint fourier i j) f

/-- Exact counting-measure complex operator norm, for all four actual variants. -/
theorem byte_degree_block_comparison (adjoint fourier : Bool) (i j : Fin 5) :
    Real.sqrt (4294967296 : ℝ) *
      ‖kernelOperator (fun y x => (block 0 (variant adjoint fourier) i j y x : ℂ))‖ ≤
        comparison i j := by
  have he := operator_norm_sq_le_of_energy
    (fun y x => (block 0 (variant adjoint fourier) i j y x : ℂ))
    ((comparison i j/65536)^2) (sq_nonneg _)
    (variant_block_complex_energy adjoint fourier i j)
  have hn := (sq_le_sq₀ (norm_nonneg _) (div_nonneg (comparison_nonneg i j) (by norm_num))).mp he
  have hs : Real.sqrt (4294967296 : ℝ) = 65536 := by
    rw [show (4294967296 : ℝ) = 65536^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs]
  linarith

end AES8.PaperWordDegreeComparison
