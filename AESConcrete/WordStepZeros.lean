import AESConcrete.WordCrossZero
import AESConcrete.WordChannelCommutation
import AESConcrete.KernelOperator

/-! Exact zero blocks of the concrete parallel-word AES step H Pi.
The diffusion is exactly AES.wordMix. These raw-step statements precede the
global nonzero-uniform centering and the fourteen exact-support refinements.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.WordStepZeros
open AESMixing WordCrossZero WordChannelCommutation

def wordStepKernel (b a : AES.WordState) : ℝ :=
  AES.parallelSuperboxKernel b (wordMixAddEquiv a)

theorem wordStepKernel_action (f : AES.WordState → ℝ) :
    action wordStepKernel f = action AES.parallelSuperboxKernel
      (fun x => f (wordMixAddEquiv.symm x)) := by
  funext y
  change (∑ a, AES.parallelSuperboxKernel y (wordMixAddEquiv.toEquiv a) * f a) =
    ∑ x, AES.parallelSuperboxKernel y x * f (wordMixAddEquiv.toEquiv.symm x)
  simpa only [Equiv.symm_apply_apply] using
    wordMixAddEquiv.toEquiv.sum_comp
      (fun x => AES.parallelSuperboxKernel y x * f (wordMixAddEquiv.toEquiv.symm x))

theorem wordStep_zero_one (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 0
      (action wordStepKernel (degreeComponent (0 : AES.Word) 1 f)) = 0 := by
  rw [wordStepKernel_action, parallel_word_activity_left]
  funext x
  exact word_degree_zero_one_apply f x

theorem wordStep_one_zero (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 1
      (action wordStepKernel (degreeComponent (0 : AES.Word) 0 f)) = 0 := by
  rw [wordStepKernel_action, ← parallel_word_degree_commutes]
  have hz : degreeComponent (0 : AES.Word) 1
      (fun x => degreeComponent (0 : AES.Word) 0 f (wordMixAddEquiv.symm x)) = 0 := by
    funext x
    exact word_degree_one_zero_apply f x
  rw [hz]
  funext x
  simp [action]

def wordStepBlock (i j : Fin 5) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (degreeKernel (0 : AES.Word) i)
    (kernelCompose wordStepKernel (degreeKernel (0 : AES.Word) j))

theorem wordStepBlock_action (i j : Fin 5) (f : AES.WordState → ℝ) :
    action (wordStepBlock i j) f = degreeComponent (0 : AES.Word) i
      (action wordStepKernel (degreeComponent (0 : AES.Word) j f)) := by
  rw [wordStepBlock, kernelCompose_action, kernelCompose_action,
    degreeKernel_action, degreeKernel_action]

theorem wordStepBlock_zero_one : wordStepBlock 0 1 = 0 := by
  apply kernel_action_ext
  intro f
  rw [wordStepBlock_action, wordStep_zero_one]
  funext x
  simp [action]

theorem wordStepBlock_one_zero : wordStepBlock 1 0 = 0 := by
  apply kernel_action_ext
  intro f
  rw [wordStepBlock_action, wordStep_one_zero]
  funext x
  simp [action]

theorem wordStepBlock_zero_one_norm : ‖kernelOperator (wordStepBlock 0 1)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [wordStepBlock_action, wordStep_zero_one]
  simp

theorem wordStepBlock_one_zero_norm : ‖kernelOperator (wordStepBlock 1 0)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [wordStepBlock_action, wordStep_one_zero]
  simp

end AESConcrete.WordStepZeros
