import AESConcrete.WordStepZeros
import AESConcrete.DegreeCentering

/-! Genuine centered AES cross-zero operators S = H Pi - U.
Here U is the global uniform-nonzero projection. It is distinct from both
the local word activity projection and the five-degree activity projection.
These statements concern whole degree spaces; finer support labels remain
a separate projection-refinement obligation.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.CenteredWordStepZeros
open AESMixing WordStepZeros DegreeCentering

theorem compose_sub_left {V : Type*} [Fintype V]
    (A B C : V → V → ℝ) :
    kernelCompose (A - B) C = kernelCompose A C - kernelCompose B C := by
  funext x y
  simp [kernelCompose, sub_mul, Finset.sum_sub_distrib]

theorem compose_sub_right {V : Type*} [Fintype V]
    (A B C : V → V → ℝ) :
    kernelCompose A (B - C) = kernelCompose A B - kernelCompose A C := by
  funext x y
  simp [kernelCompose, mul_sub, Finset.sum_sub_distrib]

theorem compose_assoc {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : V → V → ℝ) :
    kernelCompose A (kernelCompose B C) = kernelCompose (kernelCompose A B) C := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action]

def centeredWordStepKernel : AES.WordState → AES.WordState → ℝ :=
  wordStepKernel - globalUniformKernel (0 : AES.Word)

def centeredWordStepBlock (i j : Fin 5) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (degreeKernel (0 : AES.Word) i)
    (kernelCompose centeredWordStepKernel (degreeKernel (0 : AES.Word) j))

theorem centeredWordStepBlock_zero_one : centeredWordStepBlock 0 1 = 0 := by
  unfold centeredWordStepBlock centeredWordStepKernel
  rw [compose_sub_left,
    globalUniformKernel_compose_degreeKernel (0 : AES.Word)
      (by rw [AES.word_card]; norm_num) 1 (by decide), sub_zero]
  exact wordStepBlock_zero_one

theorem centeredWordStepBlock_one_zero : centeredWordStepBlock 1 0 = 0 := by
  unfold centeredWordStepBlock centeredWordStepKernel
  rw [compose_sub_left, compose_sub_right]
  change wordStepBlock 1 0 - kernelCompose (degreeKernel (0 : AES.Word) 1)
    (kernelCompose (globalUniformKernel (0 : AES.Word)) (degreeKernel (0 : AES.Word) 0)) = 0
  rw [wordStepBlock_one_zero, compose_assoc,
    degreeKernel_compose_globalUniformKernel (0 : AES.Word)
      (by rw [AES.word_card]; norm_num) 1 (by decide)]
  funext x y
  simp [kernelCompose]

theorem centeredWordStepBlock_zero_one_norm :
    ‖kernelOperator (centeredWordStepBlock 0 1)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [centeredWordStepBlock_zero_one]
  simp [action]

theorem centeredWordStepBlock_one_zero_norm :
    ‖kernelOperator (centeredWordStepBlock 1 0)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [centeredWordStepBlock_one_zero]
  simp [action]

end AESConcrete.CenteredWordStepZeros
