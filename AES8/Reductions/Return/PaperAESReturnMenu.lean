import AES8.Reductions.Return.PaperAESReturnLarge
import AES8.Reductions.Return.PaperAESReturnHS
import AES8.Reductions.Return.PaperAESReturnThin
import AES8.Recurrence.PaperWholeComparisonBridge

/-! Selection of the whole, overlap, and equal-Fourier candidates for a
proper physical return. The remaining equal-true entry resource is explicit;
dimension choices and every menu applicability condition are proved. -/
noncomputable section
namespace AES8.PaperAESReturnMenu
open AESMixing PaperKernelBounds PaperWordGraphCode PaperWordGraphDuality
open PaperAESWholeGraph PaperAESOverlapThinBound PaperThinComparisonBridge
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def primary (i j m s t : ℕ) (same : Bool) : ℚ :=
  if m ≤ s+t then
    PaperComparison.overlapLarge i j m s t (min i s) (min j t) (s-min i s) (t-min j t)
  else PaperComparison.overlapThin i j m s t (min i s) (s-min i s) (t-min j t) same

def bound (i j m dL dR : ℕ) : ℚ :=
  let s := min dL (i+m-dL)
  let t := min dR (j+m-dR)
  let same := decide ((2*dL > i+m) ↔ (2*dR > j+m))
  min (PaperComparison.wholeGraph i j m s (min j t))
    (if same then min (primary i j m s t same)
      (PaperComparison.overlapHS i j m s t (min i s) (min j t))
     else primary i j m s t same)

theorem reduced_thin_shape (m s t : ℕ) (hm : m=3 ∨ m=4)
    (hs : 0 < s) (ht : 0 < t) (hsmall : s + t < m) : ThinShape m s t := by
  unfold ThinShape
  omega

/-- The exact minimum in the paper bounds the same original physical kernel. -/
theorem proper_scaled_norm {i j m : ℕ}
    (ML UL MR UR : Finset Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hLdim : (zeroPositions ML UL).card+dL=4)
    (hRdim : (zeroPositions MR UR).card+dR=4)
    (hi : i≤4) (hj : j≤4) (hm : m=3 ∨ m=4)
    (hL0 : 0 < dL) (hL : dL < i + m) (hR0 : 0 < dR) (hR : dR < j + m)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤
      (bound i j m dL dR : ℝ) := by
  let s := min dL (i+m-dL)
  let t := min dR (j+m-dR)
  let bl := decide (2*dL>i+m)
  let br := decide (2*dR>j+m)
  have hs := reduced_dimensions i m dL hi (by omega) hL0 hL
  have ht := reduced_dimensions j m dR hj (by omega) hR0 hR
  have hsd : chosenDimension (i+m) dL bl = s := reduced_choice _ _ hL.le
  have htd : chosenDimension (j+m) dR br = t := reduced_choice _ _ hR.le
  have hsame : (bl == br) = decide ((2*dL>i+m) ↔ (2*dR>j+m)) := by
    by_cases hl : 2*dL > i+m <;> by_cases hr : 2*dR > j+m <;> simp [bl, br, hl, hr]
  have hprimary : (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤
      (primary i j m s t (bl == br) : ℝ) := by
    by_cases hlarge : m≤s+t
    · simpa only [primary, if_pos hlarge] using
        PaperAESReturnLarge.physical_large_scaled ML UL MR UR eL eR hdL hdR
          dL dR s t hLdim hRdim hL.le hR.le bl br hsd htd hs.2.1 ht.2.1 hlarge
          (by simpa only [min_comm] using hs.2.2.2)
          (by simpa only [min_comm] using ht.2.2.2)
    · have he : EntryResource false bl br := by
        intro h
        rw [h.1,h.2]
        exact hentry true
      simpa only [primary, if_neg hlarge] using
        PaperAESReturnThin.physical_thin_scaled ML UL MR UR eL eR hdL hdR
          dL dR s t hLdim hRdim hL.le hR.le bl br hsd htd hs.2.1 ht.2.1
          (reduced_thin_shape m s t hm hs.1 ht.1 (by omega)) he
  have hwhole := PaperWholeComparisonBridge.scaled_physical_norm ML UL MR UR eL eR
    hdL hdR dL dR hLdim hRdim hi hj (by omega) hL0 hL hR0 hR
  unfold bound
  change _ ≤ ((min (PaperComparison.wholeGraph i j m s (min j t))
    (if decide ((2*dL>i+m) ↔ (2*dR>j+m)) then
      min (primary i j m s t (decide ((2*dL>i+m) ↔ (2*dR>j+m))))
        (PaperComparison.overlapHS i j m s t (min i s) (min j t))
     else primary i j m s t (decide ((2*dL>i+m) ↔ (2*dR>j+m)))) : ℚ) : ℝ)
  rw [← hsame, Rat.cast_min]
  apply le_min hwhole
  by_cases heq : bl=br
  · have hh := PaperAESReturnHS.physical_hs_scaled ML UL MR UR eL eR hdL hdR
      dL dR s t hLdim hRdim hL.le hR.le bl hsd (by simpa only [heq] using htd)
      hs.2.1 ht.2.1 (hentry bl)
    simpa only [heq, beq_self_eq_true, if_true, Rat.cast_min] using le_min hprimary hh
  · simpa only [show (bl == br)=false by simp [heq], Bool.false_eq_true, if_false] using hprimary

end AES8.PaperAESReturnMenu
