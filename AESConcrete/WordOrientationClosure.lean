import AESConcrete.WordNormClosure
import AESConcrete.ByteOrientations

/-!
# Concrete oriented word-kernel intermediate bounds

The four actual byte channels and both actual MixColumns directions have
proved resource interfaces.  The same degree-block assembly therefore bounds
every composition below at the baseline coefficient 11/65536.  The transpose
residual bound is proved directly by the finite adjoint argument, rather than
assuming an identification with another two-substitution kernel.

These are explicitly defined concrete kernel compositions.  Identifying any
of them with a whole-word Fourier conjugate requires the separate tensor
Fourier, dual-diffusion, averaging-projection, and relabeling correspondence.
No such identification or certificate-strength 21/131072 bound is asserted.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordOrientationClosure
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)

def wordKernel (left right : Orientation) (inverse : Bool) :
    AES.Word → AES.Word → ℝ :=
  twoSubstitutionKernel (channel left) (channel right) (byteDiffusionOrientation inverse)

theorem word_kernel_centered_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (wordKernel left right inverse) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  WordNormSupport.aes_oriented_word_energy (channel_resources left)
    (channel_resources right) inverse f hz hs

theorem word_kernel_pointed (left right : Orientation) (inverse : Bool) :
    PointedBistochastic (wordKernel left right inverse) (0 : AES.Word) := by
  change PointedBistochastic
    (kernelCompose (substitutionKernel (channel left))
      (fun y x => substitutionKernel (channel right)
        ((byteDiffusionOrientation inverse).symm y) x)) (0 : AES.Word)
  have hleft : PointedBistochastic (substitutionKernel (channel left)) (0 : AES.Word) :=
    coordinateKernel_pointed _ _ (fun _ => (channel_resources left).pointed)
  have hright : PointedBistochastic (substitutionKernel (channel right)) (0 : AES.Word) :=
    coordinateKernel_pointed _ _ (fun _ => (channel_resources right).pointed)
  apply PointedBistochastic.compose hleft
  exact PointedBistochastic.relabel_output hright (byteDiffusionOrientation inverse)
    (byteDiffusionOrientation_zero inverse)

theorem word_kernel_residual_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix (wordKernel left right inverse) 0) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy (word_kernel_pointed left right inverse)
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) (11 / 65536)
    (word_kernel_centered_energy left right inverse) f

theorem word_kernel_transpose_pointed (left right : Orientation) (inverse : Bool) :
    PointedBistochastic (fun y x => wordKernel left right inverse x y) (0 : AES.Word) where
  nonnegative y x := (word_kernel_pointed left right inverse).nonnegative x y
  zero_row := (word_kernel_pointed left right inverse).zero_column
  zero_column := (word_kernel_pointed left right inverse).zero_row
  column_sum := (word_kernel_pointed left right inverse).row_sum
  row_sum := (word_kernel_pointed left right inverse).column_sum

theorem word_kernel_transpose_centered_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (fun y x => wordKernel left right inverse x y) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  transpose_residual_energy (wordKernel left right inverse) 0 ((11 / 65536 : ℝ) ^ 2)
    (word_kernel_pointed left right inverse).zero_column
    (word_kernel_pointed left right inverse).row_sum
    (word_kernel_centered_energy left right inverse) f hz hs

theorem word_kernel_transpose_residual_energy (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    (∑ x, action
      (residualMatrix (fun y x => wordKernel left right inverse x y) 0) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy (word_kernel_transpose_pointed left right inverse)
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) (11 / 65536)
    (word_kernel_transpose_centered_energy left right inverse) f

theorem word_kernel_residual_l2 (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    l2 (action (residualMatrix (wordKernel left right inverse) 0) f) ≤
      (11 / 65536 : ℝ) * l2 f :=
  l2_le_of_energy _ _ (11 / 65536) (by norm_num)
    (word_kernel_residual_energy left right inverse f)

theorem word_kernel_transpose_residual_l2 (left right : Orientation) (inverse : Bool)
    (f : AES.Word → ℝ) :
    l2 (action (residualMatrix (fun y x => wordKernel left right inverse x y) 0) f) ≤
      (11 / 65536 : ℝ) * l2 f :=
  l2_le_of_energy _ _ (11 / 65536) (by norm_num)
    (word_kernel_transpose_residual_energy left right inverse f)

theorem ordinary_word_kernel : wordKernel .ordinary .ordinary false = AES.wordSuperboxKernel :=
  rfl

/-- Actual forward AES word transpose, with no centered-input restriction. -/
theorem actual_word_transpose_residual_energy (f : AES.Word → ℝ) :
    (∑ x, action
      (residualMatrix (fun y x => AES.wordSuperboxKernel x y) 0) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  word_kernel_transpose_residual_energy .ordinary .ordinary false f

end AESConcrete.WordOrientationClosure
