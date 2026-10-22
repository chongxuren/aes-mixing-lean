import AES8.Reductions.Return.PaperAESNormalizedReturn
import AES8.Reductions.Return.PaperAESOverlapShortening
import AES8.Reductions.Return.PaperAESReturnTransport
import AES8.Recurrence.PaperGraphComparisonBridge

/-! Physical HS return candidate. The equal-bit pointwise resource remains
an explicit hypothesis; the ordinary case discharges it using the actual AES
entry theorem. No grouped-state estimate is assumed or asserted. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnHS
open AESMixing PaperMDSGram PaperKernelBounds PaperGraphResponseMatrix
open PaperAESWholeGraph PaperAESIncidence PaperAESNormalizedReturn PaperAESOverlapBound
open PaperAESOverlapCoordinates PaperAESReturnTransport
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

def cap (m s t : ℕ) : ℝ :=
  PaperAESOverlapHS.coefficient m s t PaperAESOverlapResources.entry
    PaperAESOverlapResources.delta PaperAESOverlapResources.total

theorem rawReturn_hs_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m) (bit : Bool)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    ‖kernelOperator (PaperWholeGraphReturn.rawReturn CL CR
      (graphCoefficient i m s) (graphCoefficient j m t) bit bit)‖ ≤
      leftFactor i m s * rightFactor j m t * cap m s t := by
  apply aes_rawReturn_norm CL CR s t hCL hCR hs ht bit bit
  have h := (aes_real_overlap_norm_le CL CR s t false bit bit).trans
    (PaperAESOverlapShortening.equal_bits_norm_of_entry CL CR s t hCL hCR hs ht false bit hentry)
  change ‖kernelOperator (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
    (Fintype.card AES.Word ^ (s-min s i)) (Fintype.card AES.Word ^ (t-min t j))
    (fun c d => ∏ k, PaperWordMixedGram.mixed false bit bit
      (middle CL c k) (middle CR d k)))‖ ≤ _
  simpa only [AESConcrete.WordFourierCore.word_card, PaperAESOverlapResources.q, cap] using h

theorem original_hs_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (bit : Bool) (hsdim : chosenDimension (i+m) dL bit = s)
    (htdim : chosenDimension (j+m) dR bit = t) (hs : s ≤ m) (ht : t ≤ m)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      leftFactor i m s * rightFactor j m t * cap m s t := by
  have hCs : IsMDS (chosenCode CL bit) s := hsdim ▸ chosenCode_isMDS CL dL hL hCL bit
  have hCt : IsMDS (chosenCode CR bit) t := htdim ▸ chosenCode_isMDS CR dR hR hCR bit
  have hcap := rawReturn_hs_norm (chosenCode CL bit) (chosenCode CR bit)
    s t hCs hCt hs ht bit hentry
  have hchosen : ‖kernelOperator (chosenReturn CL CR dL dR bit bit)‖ ≤
      leftFactor i m s * rightFactor j m t * cap m s t := by
    simpa only [chosenReturn, hsdim, htdim] using hcap
  exact original_norm_of_chosen_norm CL CR dL dR hL hR hCL hCR bit bit _
    ((norm_nonneg _).trans hchosen) hchosen

theorem original_hs_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (bit : Bool) (hsdim : chosenDimension (i+m) dL bit = s)
    (htdim : chosenDimension (j+m) dR bit = t) (hs : s ≤ m) (ht : t ≤ m)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      (PaperComparison.overlapHS i j m s t (min i s) (min j t) : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (original_hs_norm CL CR dL dR s t hL hR hCL hCR bit hsdim htdim hs ht hentry)
    (show 0 ≤ (PaperComparison.q : ℝ)^3 by norm_num [PaperComparison.q])
  exact h.trans_eq (by simpa only [cap, mul_assoc, min_comm] using
    PaperGraphComparisonBridge.hs_product i j m s t hs ht)

theorem original_ordinary_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hL : s ≤ i+m) (hR : t ≤ j+m) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (hs : s ≤ m) (ht : t ≤ m) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR s t y x : ℂ))‖ ≤
      (PaperComparison.overlapHS i j m s t (min i s) (min j t) : ℝ) :=
  original_hs_scaled CL CR s t s t hL hR hCL hCR false rfl rfl hs ht
    (PaperAESOverlapResources.ordinary_entry false)

theorem physical_hs_scaled {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (bit : Bool)
    (hsdim : chosenDimension (i+m) dL bit = s)
    (htdim : chosenDimension (j+m) dR bit = t) (hs : s ≤ m) (ht : t ≤ m)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapHS i j m s t (min i s) (min j t) : ℝ) := by
  have hcL : ML.card = i+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pL
  have hcR : MR.card = j+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pR
  rw [physicalReturn_eq ML UL MR UR pL pR hdL hdR dL dR hLdim hRdim
    (by omega) (by omega)]
  exact original_hs_scaled _ _ dL dR s t hL hR
    (PaperWordGraphDuality.physicalCode_isMDS ML UL pL dL hLdim)
    (PaperWordGraphDuality.physicalCode_isMDS MR UR pR dR hRdim)
    bit hsdim htdim hs ht hentry

end AES8.PaperAESReturnHS
