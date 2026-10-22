import AES8.Math.PaperKernelLinear
import AESMixing.KernelAlgebra

/-! Composition and finite linear combinations of literal rectangular kernels. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperKernelComposition
open AESMixing PaperKernelBounds PaperKernelLinear
set_option autoImplicit false
variable {X Y Z S T : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y]

theorem operator_comp (K : Z → Y → ℝ) (L : Y → X → ℝ) :
    kernelOperator (kernelCompose K L) = (kernelOperator K).comp (kernelOperator L) := by
  ext f z
  change (∑ x, (∑ y, K z y * L y x) * f x) = ∑ y, K z y * ∑ x, L y x * f x
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

variable [Fintype S] [Fintype T]

theorem compose_sum_left (K : S → Y → X → ℝ) (R : Z → Y → ℝ) :
    kernelCompose R (fun y x => ∑ s, K s y x) =
      fun z x => ∑ s, kernelCompose R (K s) z x := by
  funext z x
  simp only [kernelCompose, Finset.mul_sum]
  exact Finset.sum_comm

theorem compose_sum_right (K : S → Z → Y → ℝ) (R : Y → X → ℝ) :
    kernelCompose (fun z y => ∑ s, K s z y) R =
      fun z x => ∑ s, kernelCompose (K s) R z x := by
  funext z x
  simp only [kernelCompose, Finset.sum_mul]
  exact Finset.sum_comm

theorem compose_scale_left (K : Y → X → ℝ) (R : Z → Y → ℝ) (c : ℝ) :
    kernelCompose R (fun y x => c * K y x) =
      fun z x => c * kernelCompose R K z x := by
  funext z x
  simp only [kernelCompose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

theorem compose_scale_right (K : Z → Y → ℝ) (R : Y → X → ℝ) (c : ℝ) :
    kernelCompose (fun z y => c * K z y) R =
      fun z x => c * kernelCompose K R z x := by
  funext z x
  simp only [kernelCompose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

end AES8.PaperKernelComposition
