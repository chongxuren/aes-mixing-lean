import AES8.Reductions.Return.PaperAESWholeGraph
import AES8.Math.PaperEncoding

/-! Reuse the exact two-graph Fourier identity for an arbitrary chosen-return
norm cap. This transports any independently proved overlap menu bound to the
original physical orientation without adding a second residual map. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnTransport
open AESMixing PaperMDSGram PaperAESWholeGraph PaperWordGraphDuality PaperKernelBounds
set_option autoImplicit false

theorem original_real_energy_of_chosen_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool) (b : ℝ) (hb : 0 ≤ b)
    (hcap : ‖kernelOperator (chosenReturn CL CR dL dR eL eR)‖ ≤ b)
    (f : (Fin j → AES.Word) → ℝ) :
    (∑ y, action (originalReturn CL CR dL dR) f y ^ 2) ≤ b^2 * ∑ x, f x^2 := by
  rw [original_eq_chosen CL CR dL dR hL hR hCL hCR eL eR]
  simp only [kernelCompose_action]
  rw [bitF_energy]
  have h := PaperEncoding.local_energy_of_norm _ b hb hcap (action (bitF j eR) f)
  rw [bitF_energy] at h
  exact h

theorem original_norm_of_chosen_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool) (b : ℝ) (hb : 0 ≤ b)
    (hcap : ‖kernelOperator (chosenReturn CL CR dL dR eL eR)‖ ≤ b) :
    ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤ b := by
  apply (sq_le_sq₀ (norm_nonneg _) hb).mp
  apply operator_norm_sq_le_of_energy _ _ (sq_nonneg b)
  exact PaperWholeGraphReturn.complex_energy_of_real _ _
    (original_real_energy_of_chosen_norm CL CR dL dR hL hR hCL hCR eL eR b hb hcap)

theorem physical_norm_of_original_norm {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hL : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hR : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hLm : dL ≤ i+m) (hRm : dR ≤ j+m) (b : ℝ)
    (hcap : ‖kernelOperator (fun y x =>
      (originalReturn (physicalCode ML UL eL) (physicalCode MR UR eR) dL dR y x : ℂ))‖ ≤ b) :
    ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤ b := by
  have hcL : ML.card = i+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr eL
  have hcR : MR.card = j+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr eR
  rw [physicalReturn_eq ML UL MR UR eL eR hdL hdR dL dR hL hR
    (by omega) (by omega)]
  exact hcap

end AES8.PaperAESReturnTransport
