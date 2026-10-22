import AES8.Reductions.Support.PaperSupportContraction
import AES8.Reductions.Return.PaperAESActivityStepBound
import AES8.Math.PaperKernelReindex

/-! Exact coordinate join from support-frame blocks to the actual AES step.
No factorization assumption on joint vectors is introduced. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESExactSupportStep
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportOutside
open PaperSupportFrameJoin PaperSupportContraction PaperKernelBounds
open PaperAESActivityIdentification
set_option autoImplicit false
set_option maxHeartbeats 1600000

def valuesEquiv {V : Type*} {i n : ℕ} (p : Label n)
    (e : residualSet p ≃ Fin i) : (Residual p → V) ≃ (Fin i → V) :=
  { toFun := fun y k => y ((residualEquiv p).symm (e.symm k))
    invFun := fun x k => x (e (residualEquiv p k))
    left_inv := by intro y; funext k; simp
    right_inv := by intro x; funext k; simp }

theorem maskedAnalysis_eq_enum {i : ℕ} (p : Label 4) (s : Finset (Active p))
    (e : residualSet p ≃ Fin i) (y : Residual p → AES.Word) (a : AES.WordState) :
    maskedAnalysis (0 : AES.Word) p s y a =
      PaperActivityMinorTransport.analysis (residualSet p)
        (fun k => decide (k ∈ fullSet p s)) (fun k => (valuesEquiv p e y) (e k)) a := by
  simp only [valuesEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  exact (analysis_eq p s y a).symm

/-- Physical-mask and indexed-graph kernels differ only by explicit bijections. -/
theorem frameKernel_eq_contracted {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j) (adjoint : Bool)
    (y : Residual p → AES.Word) (x : Residual q → AES.Word) :
    frameKernel (0 : AES.Word) (actualStep adjoint) p q s t y x =
      contracted (residualSet p) (residualSet q) (fullSet p s) (fullSet q t) eo ei adjoint
        (valuesEquiv p eo y) (valuesEquiv q ei x) := by
  rw [frameKernel_eq]
  unfold contracted kernelCompose
  simp only [PaperActivityMinorTransport.synthesis,
    maskedAnalysis_eq_enum p s eo, maskedAnalysis_eq_enum q t ei]

theorem frameKernel_norm_eq {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j) (adjoint : Bool) :
    ‖kernelOperator (frameKernel (0 : AES.Word) (actualStep adjoint) p q s t)‖ =
      ‖kernelOperator (contracted (residualSet p) (residualSet q)
        (fullSet p s) (fullSet q t) eo ei adjoint)‖ := by
  have he := funext (fun y => funext (fun x => frameKernel_eq_contracted p q s t eo ei adjoint y x))
  rw [he]
  exact PaperKernelReindex.kernelOperator_reindex (valuesEquiv q ei) (valuesEquiv p eo) _

end AES8.PaperAESExactSupportStep
