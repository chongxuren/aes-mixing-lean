import AES8.Reductions.Support.PaperSupportFrameJoin

/-! Literal support frame kernels equal physical analysis/kernel/synthesis. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportContraction
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportCompression
open PaperSupportOutside PaperSupportFrameJoin PaperTensorCompression
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem residual_symmetric (z : V) (p : Label n) (y x : Residual p → V) :
    residualKernel z p y x = residualKernel z p x y := by
  unfold residualKernel
  apply Finset.prod_congr rfl
  intro k _
  change identityKernel (y k) (x k) - activityMatrix z (y k) (x k) =
    identityKernel (x k) (y k) - activityMatrix z (x k) (y k)
  rw [activityMatrix_symmetric]
  simp only [identityKernel, eq_comm]

/-- Equality on arbitrary joint coordinates, retaining input residual projection. -/
theorem frameKernel_eq (z : V) (K : (Fin n → V) → (Fin n → V) → ℝ)
    (p q : Label n) (s : Finset (Active p)) (t : Finset (Active q)) :
    frameKernel z K p q s t =
      kernelCompose (maskedAnalysis z p s)
        (kernelCompose K (fun a x => maskedAnalysis z q t x a)) := by
  funext y x
  unfold frameKernel kernelCompose compressed
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [← (split p).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [← (split q).symm.sum_comp]
  simp only [Fintype.sum_prod_type, maskedAnalysis, Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Residual q → V)))
    (t := (Finset.univ : Finset (Outside p → V)))]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro v _
  rw [residual_symmetric z q x a]
  simp only [PaperSupportCompression.coordinateKernel]
  ring

end AES8.PaperSupportContraction
