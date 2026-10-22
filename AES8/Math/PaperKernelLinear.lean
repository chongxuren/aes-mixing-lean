import AES8.Math.PaperKernelBounds

/-! Finite kernel formation respects the linear operations used in physical
projection expansions. These identities introduce no norm estimates. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperKernelLinear
open PaperKernelBounds
set_option autoImplicit false
variable {𝕜 X Y I : Type*} [RCLike 𝕜] [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X]

theorem operator_add (K L : Y → X → 𝕜) :
    kernelOperator (fun y x => K y x + L y x) = kernelOperator K + kernelOperator L := by
  ext f y
  simp only [kernelOperator_apply, kernelAction, add_mul, Finset.sum_add_distrib,
    ContinuousLinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply]

theorem operator_smul (a : 𝕜) (K : Y → X → 𝕜) :
    kernelOperator (fun y x => a * K y x) = a • kernelOperator K := by
  ext f y
  simp only [kernelOperator_apply, kernelAction, ContinuousLinearMap.smul_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem operator_sum (K : I → Y → X → 𝕜) :
    kernelOperator (fun y x => ∑ i, K i y x) = ∑ i, kernelOperator (K i) := by
  ext f y
  simp only [kernelOperator_apply, kernelAction, ContinuousLinearMap.sum_apply,
    WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

end AES8.PaperKernelLinear
