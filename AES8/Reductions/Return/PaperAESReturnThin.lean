import AES8.Reductions.Return.PaperAESNormalizedReturn
import AES8.Reductions.Return.PaperAESOverlapThinBound
import AES8.Reductions.Return.PaperAESReturnTransport

/-! The literal thin menu on the raw, original and marked physical return.
The operator estimate and the exact rational scalar join remain separate.
Only simultaneous Fourier requires an explicit 27/q resource. No attack,
search, grouped-state estimate or manuscript change is involved. -/
noncomputable section
namespace AES8.PaperAESReturnThin
open AESMixing PaperMDSGram PaperKernelBounds PaperGraphResponseMatrix
open PaperAESWholeGraph PaperAESIncidence PaperAESNormalizedReturn PaperAESOverlapBound
open PaperAESOverlapCoordinates PaperAESReturnTransport PaperAESOverlapThinBound
open PaperThinComparisonBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem rawReturn_thin_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (hshape : ThinShape m s t) (eL eR : Bool)
    (hentry : EntryResource false eL eR) :
    ‖kernelOperator (PaperWholeGraphReturn.rawReturn CL CR
      (graphCoefficient i m s) (graphCoefficient j m t) eL eR)‖ ≤
      leftFactor i m s * rightFactor j m t *
        thinCoefficient m s t (s-min s i) (t-min t j) (eL == eR) := by
  apply aes_rawReturn_norm CL CR s t hCL hCR hs ht eL eR
  have h := (aes_real_overlap_norm_le CL CR s t false eL eR).trans
    (physical_overlap_thin_norm CL CR s t hCL hCR hs ht hshape false eL eR hentry)
  change ‖kernelOperator (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
    (Fintype.card AES.Word ^ (s-min s i)) (Fintype.card AES.Word ^ (t-min t j))
    (fun c d => ∏ k, PaperWordMixedGram.mixed false eL eR
      (middle CL c k) (middle CR d k)))‖ ≤ _
  simpa only [AESConcrete.WordFourierCore.word_card, PaperAESOverlapResources.q] using h

theorem original_thin_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t)
    (hentry : EntryResource false eL eR) :
    ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      leftFactor i m s * rightFactor j m t *
        thinCoefficient m s t (s-min s i) (t-min t j) (eL == eR) := by
  have hCs : IsMDS (chosenCode CL eL) s := hsdim ▸ chosenCode_isMDS CL dL hL hCL eL
  have hCt : IsMDS (chosenCode CR eR) t := htdim ▸ chosenCode_isMDS CR dR hR hCR eR
  have hcap := rawReturn_thin_norm (chosenCode CL eL) (chosenCode CR eR)
    s t hCs hCt hs ht hshape eL eR hentry
  have hchosen : ‖kernelOperator (chosenReturn CL CR dL dR eL eR)‖ ≤
      leftFactor i m s * rightFactor j m t *
        thinCoefficient m s t (s-min s i) (t-min t j) (eL == eR) := by
    simpa only [chosenReturn, hsdim, htdim] using hcap
  exact original_norm_of_chosen_norm CL CR dL dR hL hR hCL hCR eL eR _
    ((norm_nonneg _).trans hchosen) hchosen

/-- The single 1600 rounding in the three-coordinate unequal-bit line
case is inherited from the scalar bridge, after the operator proof. -/
theorem original_thin_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t)
    (hentry : EntryResource false eL eR) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) (eL == eR) : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (original_thin_norm CL CR dL dR s t hL hR hCL hCR eL eR hsdim htdim hs ht hshape hentry)
    (show 0 ≤ (PaperComparison.q : ℝ)^3 by norm_num [PaperComparison.q])
  have he := thin_product_le i j m s t (s-min s i) (t-min t j) (eL == eR)
    hshape (by have := Nat.min_le_right i s; omega) (by have := Nat.min_le_right j t; omega)
  exact h.trans (by simpa only [mul_assoc, min_comm] using he)

/-- The rational thin candidate on the literal marked physical return.
Chosen dimensions and the equal-true resource are explicit inputs. -/
theorem physical_thin_scaled {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t)
    (hentry : EntryResource false eL eR) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) (eL == eR) : ℝ) := by
  have hcL : ML.card = i+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pL
  have hcR : MR.card = j+m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr pR
  rw [physicalReturn_eq ML UL MR UR pL pR hdL hdR dL dR hLdim hRdim
    (by omega) (by omega)]
  exact original_thin_scaled _ _ dL dR s t hL hR
    (PaperWordGraphDuality.physicalCode_isMDS ML UL pL dL hLdim)
    (PaperWordGraphDuality.physicalCode_isMDS MR UR pR dR hRdim)
    eL eR hsdim htdim hs ht hshape hentry

/-- The ordinary thin menu has no residual resource premise. -/
theorem original_ordinary_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hL : s ≤ i+m) (hR : t ≤ j+m) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR s t y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) true : ℝ) :=
  original_thin_scaled CL CR s t s t hL hR hCL hCR false false rfl rfl hs ht hshape
    (entryResource_ordinary false)

/-- Both unequal Fourier choices have certified local moments and need
no pointwise entry premise. -/
theorem original_oneSided_scaled {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (dL dR s t : ℕ)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (hCL : IsMDS CL dL) (hCR : IsMDS CR dR)
    (side : Bool)
    (hsdim : chosenDimension (i+m) dL side = s)
    (htdim : chosenDimension (j+m) dR (!side) = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (originalReturn CL CR dL dR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) false : ℝ) := by
  have h := original_thin_scaled CL CR dL dR s t hL hR hCL hCR side (!side)
    hsdim htdim hs ht hshape (entryResource_oneSided false side)
  cases side <;> exact h

/-- Ordinary endpoint on the literal marked physical return. -/
theorem physical_ordinary_scaled {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+s=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+t=4)
    (hL : s ≤ i+m) (hR : t ≤ j+m)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) true : ℝ) :=
  physical_thin_scaled ML UL MR UR pL pR hdL hdR s t s t hLdim hRdim hL hR
    false false rfl rfl hs ht hshape (entryResource_ordinary false)

/-- Unequal endpoint on the literal marked physical return, for either side. -/
theorem physical_oneSided_scaled {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (side : Bool)
    (hsdim : chosenDimension (i+m) dL side = s)
    (htdim : chosenDimension (j+m) dR (!side) = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) false : ℝ) := by
  have h := physical_thin_scaled ML UL MR UR pL pR hdL hdR dL dR s t hLdim hRdim hL hR
    side (!side) hsdim htdim hs ht hshape (entryResource_oneSided false side)
  cases side <;> exact h

end AES8.PaperAESReturnThin
