import AES8.Estimates.Word.PaperAESCompleteResources
import AES8.Reductions.Return.PaperAESReturnMenu
import AES8.Reductions.Return.PaperAESReturnFrameBound
import AES8.Estimates.FirstHigh.PaperAESSeveralFirstReturn

/-!
# Physical estimates from complete finite resources

This leaf instantiates the entry resources of the existing actual graph and
source estimates. Geometric hypotheses and arbitrary signed or complex input
domains remain explicit. Startup consumes the current OrdinaryBound interface
through the proved raw predicate adapter. Already unconditional estimates
retain their own proofs.
-/

noncomputable section
namespace AES8.PaperAESCompleteEstimates
open AESMixing PaperComparison TransferAssembly SupportEvolution
open PaperKernelBounds PaperWordGraphCode PaperWordGraphDuality
open PaperAESWholeGraph PaperAESOverlapThinBound PaperThinComparisonBridge
open PaperAESReturnIdentification PaperAESTwoRoundSource
open AESPaper.GroupedLaw (error)
open PaperAESCompleteResources
set_option autoImplicit false
set_option maxRecDepth 10000

/-- HS expression for every applicable equal-bit reduced representation. -/
theorem overlap_hs {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (bit : Bool)
    (hsdim : chosenDimension (i+m) dL bit = s)
    (htdim : chosenDimension (j+m) dR bit = t) (hs : s ≤ m) (ht : t ≤ m) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapHS i j m s t (min i s) (min j t) : ℝ) :=
  PaperAESReturnHS.physical_hs_scaled ML UL MR UR pL pR hdL hdR
    dL dR s t hLdim hRdim hL hR bit hsdim htdim hs ht (mixed_entry bit)

/-- All four thin shapes, every outside dimension and both Fourier choices. -/
theorem overlap_thin {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (pL : ML ≃ Fin i ⊕ Fin m) (pR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR s t : ℕ)
    (hLdim : (PaperWordGraphCode.zeroPositions ML UL).card+dL=4)
    (hRdim : (PaperWordGraphCode.zeroPositions MR UR).card+dR=4)
    (hL : dL ≤ i+m) (hR : dR ≤ j+m) (eL eR : Bool)
    (hsdim : chosenDimension (i+m) dL eL = s)
    (htdim : chosenDimension (j+m) dR eR = t)
    (hs : s ≤ m) (ht : t ≤ m) (hshape : ThinShape m s t) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR pL pR y x : ℂ))‖ ≤
      (PaperComparison.overlapThin i j m s t (min i s)
        (s-min i s) (t-min j t) (eL == eR) : ℝ) := by
  have he : EntryResource false eL eR := by
    intro h
    rw [h.1, h.2]
    exact mixed_entry true
  exact PaperAESReturnThin.physical_thin_scaled ML UL MR UR pL pR hdL hdR
    dL dR s t hLdim hRdim hL hR eL eR hsdim htdim hs ht hshape he

/-- Paper lem:aesasm-overlap-menu: the selected same-kernel minimum.
The large expression is the already unconditional physical_large_scaled;
overlap_hs and overlap_thin above expose all other applicable expressions. -/
theorem overlap_menu {i j m : ℕ}
    (ML UL MR UR : Finset Position)
    (eL : ML ≃ Fin i ⊕ Fin m) (eR : MR ≃ Fin j ⊕ Fin m)
    (hdL : Disjoint ML UL) (hdR : Disjoint MR UR) (dL dR : ℕ)
    (hLdim : (zeroPositions ML UL).card+dL=4)
    (hRdim : (zeroPositions MR UR).card+dR=4)
    (hi : i≤4) (hj : j≤4) (hm : m=3 ∨ m=4)
    (hL0 : 0 < dL) (hL : dL < i + m) (hR0 : 0 < dR) (hR : dR < j + m) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (fun y x => (physicalReturn ML UL MR UR eL eR y x : ℂ))‖ ≤
      (PaperAESReturnMenu.bound i j m dL dR : ℝ) :=
  PaperAESReturnMenu.proper_scaled_norm ML UL MR UR eL eR hdL hdR
    dL dR hLdim hRdim hi hj hm hL0 hL hR0 hR mixed_entry

/-- Paper prop:aesasm-return: signed shared metric once on actual frames. -/
theorem return_frame {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (outsideContract O I A B eo ei ReturnCentering.physicalReturnKernel)‖ ≤
      (PaperComparison.returnGraph i (A \ O).card j (B \ I).card : ℝ) :=
  PaperAESReturnFrameBound.high_scaled_norm O I A B eo ei mixed_entry

/-- Paper prop:aes-profile: all four actual current physical estimates.
PhysicalCaps has arbitrary signed-input low/high fields and the actual-source
firstHigh field; PhysicalEstimates adds the actual four-round initializer. -/
theorem profile_estimates : PaperCurrentRecurrence.PhysicalEstimates :=
  PaperAESFromEntries.physicalEstimates ordinary_raw_bound fourier_raw_bound

/-- Stronger all 14-coordinate startup, before weakening 900 to 1000. -/
theorem initial_900 (a : AES.State) (ha : a ≠ 0) (c : Fin 14) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (900 * (PaperComparison.startup0 c : ℝ)) :=
  PaperAESCurrentStartup.initial_900
    (PaperSharpEntriesProfiles.ordinary_bound ordinary_raw_bound) a ha c

/-- Paper prop:aesasm-initial, in the actual unnormalized component units. -/
theorem initial (a : AES.State) (ha : a ≠ 0) (c : Fin 14) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (1000 * (PaperComparison.startup0 c : ℝ)) :=
  PaperAESCurrentStartup.initial
    (PaperSharpEntriesProfiles.ordinary_bound ordinary_raw_bound) a ha c

/-- Paper lem:aesasm-several-source-return, preserving support 2..4. -/
theorem several_source_first_return (a : AES.State) (ha : a ≠ 0)
    (hw : 2 ≤ PaperSupportProjection.supportCount (sourceMask a))
    (i : Fin 14) :
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * (firstReturn i : ℝ)) :=
  PaperAESSeveralFirstReturn.firstHigh_le a ha hw mixed_entry i

#print axioms overlap_hs
#print axioms overlap_thin
#print axioms overlap_menu
#print axioms return_frame
#print axioms profile_estimates
#print axioms initial_900
#print axioms initial
#print axioms several_source_first_return
end AES8.PaperAESCompleteEstimates
