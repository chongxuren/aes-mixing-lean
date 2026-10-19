import AESConcrete.DampedDegreeThree
import AESConcrete.ReverseDegreeThree
import AESConcrete.SharpActivityZero
import AESConcrete.WordOrientationClosure
import AESConcrete.KernelOperator

/-!
# The sharp directly damped AES word bound

The two activity/degree-three entries are bounded after both substitutions,
using the actual forward and reverse projected-input energy theorems.  Only
the degree-zero raw diffusion cap is changed in the remaining generic block
assembly.  In particular, no sharper raw degree-three cap is assumed here.

An exact positive-vector certificate assembles these concrete bounds at
21/131072 = 10.5/65536.  The resulting energy and operator bounds quantify
over arbitrary joint four-byte inputs.  Whole-word Fourier identification,
round assembly, and a complete AES 10/14/16 theorem remain separate work.
Constructive mathematics only: no cryptanalytic attacks or reproduction.
-/

noncomputable section
open scoped BigOperators Matrix

namespace AESConcrete.SharpDampedWordNorm
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed
  word_kernel_transpose_pointed)

set_option maxRecDepth 100000

/-- The raw comparison changes only the separately proved degree-zero cap.
The actual degree-three improvement enters `directComparison` after damping. -/
def rawZeroCaps (i j : Fin 5) : ℝ :=
  if i = 0 ∧ j = 0 then 63 / 655360 else byteComparison i j

theorem rawZeroCaps_nonneg (i j : Fin 5) : 0 ≤ rawZeroCaps i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rawZeroCaps, byteComparison]

theorem rawZeroCaps_energy (inverse : Bool) (i j : Fin 5)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, degreeTransfer 0 i j (byteDiffusionOrientation inverse) f x ^ 2) ≤
      (rawZeroCaps i j) ^ 2 * ∑ x, degreeComponent 0 j f x ^ 2 := by
  by_cases h : i = 0 ∧ j = 0
  · rcases h with ⟨rfl, rfl⟩
    simpa [rawZeroCaps] using
      SharpActivityZero.sharp_activity_zero_energy inverse f hz hs
  · simpa only [rawZeroCaps, if_neg h] using
      WordNormSupport.aes_byte_diffusion_comparison inverse i j f hz hs

/-- Directly damped degree-three caps, with generic damping elsewhere. -/
def directComparison (i j : Fin 5) : ℝ :=
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 33 / (10 * 65536)
  else WordNorm.dampedCaps rawZeroCaps i j

theorem directComparison_nonneg (i j : Fin 5) : 0 ≤ directComparison i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [directComparison, WordNorm.dampedCaps, rawZeroCaps, byteComparison,
      Fin.ext_iff]

theorem directComparison_symmetric (i j : Fin 5) :
    directComparison i j = directComparison j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [directComparison, WordNorm.dampedCaps, rawZeroCaps, byteComparison,
      Fin.ext_iff]

/-- This witness is checked against all five rows of the new comparison. -/
def comparisonWitness : Fin 5 → ℝ := ![50, 9, 28, 18, 8]

theorem comparisonWitness_pos (i : Fin 5) : 0 < comparisonWitness i := by
  fin_cases i <;> norm_num [comparisonWitness]

private theorem sum_fin_zero (f : Fin 0 → ℝ) : (∑ i, f i) = 0 := by simp

/-- Expand an opaque summand before normalizing concrete comparison entries,
so recursive successor lambdas do not enter the rational simplification. -/
private theorem sum_fin_five (f : Fin 5 → ℝ) :
    (∑ j : Fin 5, f j) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) := by
  simp only [Fin.sum_univ_succ, sum_fin_zero]
  rfl

theorem comparison_certificate (i : Fin 5) :
    (∑ j, directComparison i j * comparisonWitness j) <
      (21 / 131072 : ℝ) * comparisonWitness i := by
  rw [sum_fin_five]
  fin_cases i <;>
    norm_num [directComparison, WordNorm.dampedCaps, rawZeroCaps, byteComparison,
      comparisonWitness, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]

theorem comparison_energy (x : Fin 5 → ℝ) :
    (∑ i, action directComparison x i ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ j, x j ^ 2 := by
  exact weighted_schur_energy directComparison comparisonWitness (21 / 131072)
    (by norm_num) directComparison_nonneg directComparison_symmetric
    comparisonWitness_pos (fun i => le_of_lt (comparison_certificate i)) x

/-- Centering is proved for the projected input before removing the residual
matrix.  The activity term is not discarded for an arbitrary input. -/
theorem residual_action_degree_eq (left right : Orientation) (inverse : Bool)
    (j : Fin 5) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (residualMatrix (wordKernel left right inverse) 0)
        (degreeComponent 0 j f) =
      action (wordKernel left right inverse) (degreeComponent 0 j f) := by
  have hc := degreeComponent_centered (0 : BinaryWord 8)
    (by norm_num [BinaryWord.card]) j f hz hs
  rw [residualMatrix_action (word_kernel_pointed left right inverse),
    wordResidual_eq_self 0 _ hc.1 hc.2]

/-- Actual projected word blocks, retaining each projected-input norm. -/
theorem direct_degree_bound (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    l2 (degreeComponent 0 i
      (action (wordKernel left right inverse) (degreeComponent 0 j f))) ≤
      directComparison i j * l2 (degreeComponent 0 j f) := by
  by_cases h03 : i = 0 ∧ j = 3
  · rcases h03 with ⟨rfl, rfl⟩
    have h := ReverseDegreeThree.actual_reverse_degree_three_energy left right inverse f
    rw [residual_action_degree_eq left right inverse 3 f hz hs] at h
    simpa [directComparison] using
      (l2_le_of_energy _ _ (33 / (10 * 65536)) (by norm_num) h)
  · by_cases h30 : i = 3 ∧ j = 0
    · rcases h30 with ⟨rfl, rfl⟩
      have h := DampedDegreeThree.actual_forward_degree_three_energy left right inverse f
      rw [residual_action_degree_eq left right inverse 0 f hz hs] at h
      simpa [directComparison] using
        (l2_le_of_energy _ _ (33 / (10 * 65536)) (by norm_num) h)
    · have h := WordNorm.two_substitution_degree_bound_of_caps
        (channel_resources left) (channel_resources right)
        (byteDiffusionOrientation inverse) rawZeroCaps rawZeroCaps_nonneg
        (rawZeroCaps_energy inverse) i j f hz hs
      simpa only [directComparison, if_neg (not_or_intro h03 h30), wordKernel] using h

theorem word_kernel_centered_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (wordKernel left right inverse) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  exact degree_matrix_energy 0 (by norm_num [BinaryWord.card])
    (wordKernel left right inverse) directComparison (21 / 131072)
    directComparison_nonneg comparison_energy f
    (fun i j => direct_degree_bound left right inverse i j f hz hs)

theorem word_kernel_residual_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix (wordKernel left right inverse) 0) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy (word_kernel_pointed left right inverse)
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) (21 / 131072)
    (word_kernel_centered_energy left right inverse) f

theorem word_kernel_transpose_centered_energy
    (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (fun y x => wordKernel left right inverse x y) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  transpose_residual_energy (wordKernel left right inverse) 0
    ((21 / 131072 : ℝ) ^ 2)
    (word_kernel_pointed left right inverse).zero_column
    (word_kernel_pointed left right inverse).row_sum
    (word_kernel_centered_energy left right inverse) f hz hs

theorem word_kernel_transpose_residual_energy
    (left right : Orientation) (inverse : Bool) (f : AES.Word → ℝ) :
    (∑ x, action
      (residualMatrix (fun y x => wordKernel left right inverse x y) 0) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy (word_kernel_transpose_pointed left right inverse)
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) (21 / 131072)
    (word_kernel_transpose_centered_energy left right inverse) f

theorem word_kernel_residual_l2 (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    l2 (action (residualMatrix (wordKernel left right inverse) 0) f) ≤
      (21 / 131072 : ℝ) * l2 f :=
  l2_le_of_energy _ _ (21 / 131072) (by norm_num)
    (word_kernel_residual_energy left right inverse f)

theorem word_kernel_transpose_residual_l2
    (left right : Orientation) (inverse : Bool) (f : AES.Word → ℝ) :
    l2 (action (residualMatrix
      (fun y x => wordKernel left right inverse x y) 0) f) ≤
      (21 / 131072 : ℝ) * l2 f :=
  l2_le_of_energy _ _ (21 / 131072) (by norm_num)
    (word_kernel_transpose_residual_energy left right inverse f)

theorem word_kernel_residual_operator_norm_le
    (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (residualMatrix (wordKernel left right inverse) 0)‖ ≤
      (21 / 131072 : ℝ) :=
  kernelOperator_norm_le _ (by norm_num)
    (word_kernel_residual_energy left right inverse)

theorem word_kernel_transpose_residual_operator_norm_le
    (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (residualMatrix
      (fun y x => wordKernel left right inverse x y) 0)‖ ≤
      (21 / 131072 : ℝ) :=
  kernelOperator_norm_le _ (by norm_num)
    (word_kernel_transpose_residual_energy left right inverse)

theorem word_superbox_centered_energy (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action AES.wordSuperboxKernel f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  word_kernel_centered_energy .ordinary .ordinary false f hz hs

theorem word_superbox_residual_energy (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix AES.wordSuperboxKernel 0) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  word_kernel_residual_energy .ordinary .ordinary false f

theorem word_superbox_transpose_residual_energy (f : AES.Word → ℝ) :
    (∑ x, action
      (residualMatrix (fun y x => AES.wordSuperboxKernel x y) 0) f x ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  word_kernel_transpose_residual_energy .ordinary .ordinary false f

theorem wordResidualOperator_norm_le :
    ‖wordResidualOperator‖ ≤ (21 / 131072 : ℝ) :=
  word_kernel_residual_operator_norm_le .ordinary .ordinary false

theorem word_superbox_transpose_residual_operator_norm_le :
    ‖kernelOperator
      (residualMatrix (fun y x => AES.wordSuperboxKernel x y) 0)‖ ≤
      (21 / 131072 : ℝ) :=
  word_kernel_transpose_residual_operator_norm_le .ordinary .ordinary false

end AESConcrete.SharpDampedWordNorm
