import AESConcrete.WordFourierBounds

/-!
# Four concrete word residual variants

The flags below denote actual transpose and whole-word Fourier operations
on the ordinary AES residual, so the exported bounds directly cover
R, R^T, F R F and F R^T F. The one-sided mixed matrices R F and F R
require their separate entry resource. No full round theorem is claimed.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordFourierVariants
open AESMixing
open AESConcrete.WordFourierCore (wordConjugate)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.WordFourierBounds
set_option maxRecDepth 100000

def baseResidual (adjoint : Bool) : AES.Word → AES.Word → ℝ :=
  if adjoint then fun y x => residualMatrix AES.wordSuperboxKernel 0 x y
  else residualMatrix AES.wordSuperboxKernel 0

def variant (adjoint fourier : Bool) : AES.Word → AES.Word → ℝ :=
  if fourier then wordConjugate (baseResidual adjoint) else baseResidual adjoint

def baseOrientation (adjoint : Bool) : ByteOrientations.Orientation :=
  if adjoint then .transposed else .ordinary

theorem baseResidual_eq (adjoint : Bool) :
    baseResidual adjoint =
      residualMatrix (wordKernel (baseOrientation adjoint) (baseOrientation adjoint) adjoint) 0 := by
  cases adjoint
  · rfl
  · funext y x
    exact ReverseDegreeThree.residual_transpose .ordinary .ordinary false x y

theorem variant_entry_lt (adjoint fourier : Bool) (a b : AES.Word) :
    |variant adjoint fourier b a| < (46 / 4294967296 : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact ActualWordEntry.residual_entry_lt _ _ _ a b
  · exact fourier_residual_entry_lt _ _ _ a b

theorem variant_column_energy_lt (adjoint fourier : Bool) (a : AES.Word) :
    (∑ y, variant adjoint fourier y a ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact AllColumnBound.residual_column_energy_lt _ _ _ a
  · exact fourier_residual_column_energy_lt _ _ _ a

theorem variant_trace_lt (adjoint fourier : Bool) :
    (∑ y, ∑ x, variant adjoint fourier y x ^ 2) < (4251 / 4294967296 : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact ActualWordMoments.actual_trace_bound _ _ _
  · exact fourier_residual_trace_lt _ _ _

theorem variant_gram_moment_lt (adjoint fourier : Bool) :
    (∑ x, ∑ z, (∑ y, variant adjoint fourier y x * variant adjoint fourier y z)^2) <
      (300 / 4294967296 : ℝ)^2 := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact ActualWordMoments.actual_gram_moment_bound _ _ _
  · exact fourier_residual_gram_moment_lt _ _ _

theorem variant_operator_norm_le (adjoint fourier : Bool) :
    ‖kernelOperator (variant adjoint fourier)‖ ≤ (21 / 131072 : ℝ) := by
  unfold variant
  rw [baseResidual_eq]
  cases fourier
  · exact SharpDampedWordNorm.word_kernel_residual_operator_norm_le _ _ _
  · exact fourier_residual_operator_norm_le _ _ _

end AESConcrete.WordFourierVariants
