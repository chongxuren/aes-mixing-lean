/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.WordFourierVariants
import AES8.Estimates.Word.PaperDampedDegreeBounds

/-!
# Reassemble the inherited word blocks at the sharper constant

The shared paper bound uses literal parity for degree three and literal
slope spectral estimates for degree two. The printed comparison table and
this positive-vector certificate assemble those blocks. A small strict
margin gives the manuscript's
52/(5 sqrt(q)) bound for all four actual residual orientations.
Constructive proof only; no manuscript or predecessor changes.
-/

noncomputable section
open scoped BigOperators Matrix
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AES8.SharpWordNorm
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open PaperWordDegreeComparison (comparison normalizedComparison
  normalizedComparison_nonneg normalizedComparison_symmetric)

def witness : Fin 5 → ℝ := ![500, 94, 281, 182, 79]

-- A strict rational margin avoids a separate strict operator-norm argument.
def rho : ℝ := 10399 / (1000 * 65536)

theorem witness_pos (i : Fin 5) : 0 < witness i := by
  fin_cases i <;> norm_num [witness]

private theorem sum_fin_zero (f : Fin 0 → ℝ) : (∑ i, f i) = 0 := by simp

private theorem sum_fin_five (f : Fin 5 → ℝ) :
    (∑ j, f j) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) := by
  simp only [Fin.sum_univ_succ, sum_fin_zero]
  rfl

theorem comparison_certificate (i : Fin 5) :
    (∑ j, normalizedComparison i j * witness j) < rho * witness i := by
  rw [sum_fin_five]
  fin_cases i <;>
    norm_num [normalizedComparison, comparison, witness, rho, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem comparison_energy (x : Fin 5 → ℝ) :
    (∑ i, action normalizedComparison x i ^ 2) ≤ rho ^ 2 * ∑ j, x j ^ 2 :=
  weighted_schur_energy normalizedComparison witness rho (by norm_num [rho])
    normalizedComparison_nonneg normalizedComparison_symmetric witness_pos
    (fun i => (comparison_certificate i).le) x

theorem centered_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (wordKernel left right inverse) f x ^ 2) ≤
      rho ^ 2 * ∑ x, f x ^ 2 :=
  degree_matrix_energy 0 (by norm_num [BinaryWord.card])
    (wordKernel left right inverse) normalizedComparison rho
    normalizedComparison_nonneg comparison_energy f
    (fun i j => PaperDampedDegreeBounds.direct_degree_bound left right inverse i j f hz hs)

theorem residual_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix (wordKernel left right inverse) 0) f x ^ 2) ≤
      rho ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy (word_kernel_pointed left right inverse)
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) rho
    (centered_energy left right inverse) f

theorem fourier_residual_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ y, action (WordFourierCore.wordConjugate
      (residualMatrix (wordKernel left right inverse) 0)) f y ^ 2) ≤
      rho ^ 2 * ∑ x, f x ^ 2 := by
  rw [WordFourierClosure.residual_fourier, WordFourierBounds.reverse_energy]
  have h := residual_energy
    (FourierLineOverlap.fourierMate left) (FourierLineOverlap.fourierMate right)
    (!inverse) (fun x => f (WordFourierDiffusion.wordReverse x))
  have hn : (∑ x, f (WordFourierDiffusion.wordReverse x) ^ 2) = ∑ x, f x ^ 2 :=
    Equiv.sum_comp WordFourierDiffusion.wordReverse (fun x => f x ^ 2)
  rw [hn] at h
  exact h

theorem variant_energy (adjoint fourier : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (WordFourierVariants.variant adjoint fourier) f y ^ 2) ≤
      rho ^ 2 * ∑ x, f x ^ 2 := by
  unfold WordFourierVariants.variant
  rw [WordFourierVariants.baseResidual_eq]
  cases fourier
  · exact residual_energy _ _ _ f
  · exact fourier_residual_energy _ _ _ f

theorem variant_operator_norm_le (adjoint fourier : Bool) :
    ‖kernelOperator (WordFourierVariants.variant adjoint fourier)‖ ≤ rho :=
  kernelOperator_norm_le _ (by norm_num [rho]) (variant_energy adjoint fourier)

/-- The actual four variants satisfy the new paper's local norm resource. -/
theorem variant_operator_norm_lt (adjoint fourier : Bool) :
    ‖kernelOperator (WordFourierVariants.variant adjoint fourier)‖ <
      52 / (5 * Real.sqrt ((2 : ℝ) ^ 32)) := by
  apply (variant_operator_norm_le adjoint fourier).trans_lt
  have hs : Real.sqrt ((2 : ℝ) ^ 32) = 65536 := by
    rw [show (2 : ℝ) ^ 32 = 65536 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
  rw [hs]
  norm_num [rho]

end AES8.SharpWordNorm
