import AES8.Reductions.Return.PaperAESNormalizedReturn
import AES8.Reductions.Return.PaperAESOverlapCoordinates
import AES8.Reductions.Return.PaperAESReturnTransport
import AES8.Recurrence.PaperGraphComparisonBridge

/-! The large-overlap menu bound on the actual chosen and original return
operators. Both outside fiber normalizers are retained until exact incidence
factorization; scalar Q^3 collection is then applied to the same norm cap. -/
noncomputable section
namespace AES8.PaperAESReturnLarge
open AESMixing PaperMDSGram PaperKernelBounds PaperGraphResponseMatrix
open PaperAESWholeGraph PaperAESIncidence PaperAESNormalizedReturn PaperAESOverlapBound
open PaperAESOverlapCoordinates PaperAESReturnTransport
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

theorem rawReturn_large_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (hlarge : m ≤ s+t) (ha : s-min s i ≤ m-s) (hb : t-min t j ≤ m-t)
    (eL eR : Bool) :
    ‖kernelOperator (PaperWholeGraphReturn.rawReturn CL CR
      (graphCoefficient i m s) (graphCoefficient j m t) eL eR)‖ ≤
      leftFactor i m s * rightFactor j m t * paperCoefficient m s t (s-min s i) (t-min t j) := by
  apply aes_rawReturn_norm CL CR s t hCL hCR hs ht eL eR
  have hreal := aes_real_overlap_norm_le CL CR s t false eL eR
  have hlarge' := information_overlap_paper_norm CL CR s t hCL hCR 0 0
    (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m))
    (by simpa only [Fintype.card_fin] using hs)
    (by simpa only [Fintype.card_fin] using ht)
    (by simpa only [Fintype.card_fin] using hlarge)
    (leftPositions (I := Fin i) (M := Fin m))
    (leftPositions (I := Fin j) (M := Fin m))
    outside_middle_disjoint outside_middle_disjoint
    (by simpa only [leftPositions_card, Fintype.card_fin] using ha)
    (by simpa only [leftPositions_card, Fintype.card_fin] using hb) false eL eR
  have h := hreal.trans hlarge'
  change ‖kernelOperator (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
    (Fintype.card AES.Word ^ (s-min s i)) (Fintype.card AES.Word ^ (t-min t j))
    (fun c d => ∏ k, PaperWordMixedGram.mixed false eL eR
      (middle CL c k) (middle CR d k)))‖ ≤ _
  simpa only [
    AESConcrete.WordFourierCore.word_card, PaperAESOverlapResources.q,
    leftPositions_card, Fintype.card_fin] using h

theorem original_large_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hlarge : m ≤ s+t)
    (ha : s-min s i ≤ m-s) (hb : t-min t j ≤ m-t) :
    ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      leftFactor i m s * rightFactor j m t * paperCoefficient m s t (s-min s i) (t-min t j) := by
  have hCs : IsMDS (chosenCode CL eL) s := hsdim ▸ chosenCode_isMDS CL dL hL hCL eL
  have hCt : IsMDS (chosenCode CR eR) t := htdim ▸ chosenCode_isMDS CR dR hR hCR eR
  have hcap := rawReturn_large_norm (chosenCode CL eL) (chosenCode CR eR)
    s t hCs hCt hs ht hlarge ha hb eL eR
  have hchosen : ‖kernelOperator (chosenReturn CL CR dL dR eL eR)‖ ≤
      leftFactor i m s * rightFactor j m t * paperCoefficient m s t (s-min s i) (t-min t j) := by
    simpa only [chosenReturn, hsdim, htdim] using hcap
  exact original_norm_of_chosen_norm CL CR dL dR hL hR hCL hCR eL eR _
    ((norm_nonneg _).trans hchosen) hchosen

/-- Literal rational large candidate on the original complex return. -/
theorem original_large_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hlarge : m ≤ s+t)
    (ha : s-min s i ≤ m-s) (hb : t-min t j ≤ m-t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      (PaperComparison.overlapLarge i j m s t (min i s) (min j t)
        (s-min i s) (t-min j t) : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (original_large_norm CL CR dL dR s t hL hR hCL hCR eL eR hsdim htdim hs ht hlarge ha hb)
    (show 0 ≤ (PaperComparison.q : ℝ)^3 by norm_num [PaperComparison.q])
  have he := PaperGraphComparisonBridge.large_product i j m s t hlarge hs ht
    (by simpa only [min_comm] using ha) (by simpa only [min_comm] using hb)
  exact h.trans_eq (by simpa only [mul_assoc, min_comm] using he)

/-- The same rational candidate on the literal marked physical return. The
chosen dimensions are explicit so a later menu can minimize over both sides. -/
theorem physical_large_scaled {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hlarge : m ≤ s+t)
    (ha : s-min s i ≤ m-s) (hb : t-min t j ≤ m-t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapLarge i j m s t (min i s) (min j t)
        (s-min i s) (t-min j t) : ℝ) := by
  have hcL : ML.card = i+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pL
  have hcR : MR.card = j+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pR
  rw [physicalReturn_eq ML UL MR UR pL pR hdL hdR dL dR hLdim hRdim
    (by omega) (by omega)]
  exact original_large_scaled _ _ dL dR s t hL hR
    (PaperWordGraphDuality.physicalCode_isMDS ML UL pL dL hLdim)
    (PaperWordGraphDuality.physicalCode_isMDS MR UR pR dR hRdim)
    eL eR hsdim htdim hs ht hlarge ha hb

end AES8.PaperAESReturnLarge
