import AES8.Math.PaperUnshortenedCode
import AES8.Reductions.Return.PaperAESOverlapCoordinates
import AES8.Reductions.Return.PaperAESOverlapHS

/-! Reuse physical-shortening overlap estimates on the literal incidence codes.
All source points and outside labels are reindexed by explicit equivalences;
the fiber normalizers retain their exact dimensions. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESOverlapShortening
open AESMixing PaperMDSGram PaperMDSOverlap PaperMDSShortening
open PaperUnshortenedCode PaperFiberKernel PaperKernelBounds PaperAESIncidence
open PaperGraphResponseMatrix PaperAESOverlapBound
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

def shortening {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (s : ℕ) (hC : IsMDS C s) (hs : s ≤ m) :
    PhysicalShortening (Fin i ⊕ Fin m) AES.Word s m :=
  asShortening C s m (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    hC 0 (middleEmbedding (Fin i) (Fin m))
    (leftPositions (I := Fin i) (M := Fin m)) (fun k => not_mem_leftPositions_inr k)

@[simp] theorem shortening_fiberDimension {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (s : ℕ) (hC : IsMDS C s) (hs : s ≤ m) :
    (shortening C s hC hs).fiberDimension = s-min s i := by
  simp only [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
    shortening, asShortening, leftPositions_card, Fintype.card_fin]

theorem physical_overlap_norm_eq {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (adjoint eL eR : Bool) :
    ‖PaperAESOverlapLarge.overlap CL CR s t 0 0
      (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m))
      (leftPositions (I := Fin i) (M := Fin m))
      (leftPositions (I := Fin j) (M := Fin m)) adjoint eL eR‖ =
    ‖PaperAESOverlapHS.normalizedOverlap (shortening CL s hCL hs)
      (shortening CR t hCR ht) (fun _ => PaperWordMixedGram.mixed adjoint eL eR)‖ := by
  rw [PaperAESOverlapLarge.overlap, ← compression_eq_adjoint_comp]
  simp only [PaperPhysicalOverlap.physicalMiddleKernel, Complex.ofReal_prod]
  rw [compressed_norm_eq CL CR 0 0
    (leftPositions (I := Fin i) (M := Fin m)) (leftPositions (I := Fin j) (M := Fin m))
    (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m))
    (fun _ y x => (PaperWordMixedGram.mixed adjoint eL eR y x : ℂ))]
  rw [PaperAESOverlapHS.normalizedOverlap, ← compression_eq_adjoint_comp]
  simp only [PhysicalShortening.projection, shortening, asShortening,
    PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
    leftPositions_card, Fintype.card_fin, AESConcrete.WordFourierCore.word_card,
    PaperAESOverlapHS.rawKernel, PaperAESOverlapHS.shortMiddle, Complex.ofReal_prod]
  rfl

theorem equal_bits_norm_of_entry {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (adjoint bit : Bool)
    (hentry : ∀ y x, |PaperWordMixedGram.mixed adjoint bit bit y x| ≤ PaperAESOverlapResources.entry) :
    ‖PaperAESOverlapLarge.overlap CL CR s t 0 0
      (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m))
      (leftPositions (I := Fin i) (M := Fin m))
      (leftPositions (I := Fin j) (M := Fin m)) adjoint bit bit‖ ≤
      PaperAESOverlapHS.coefficient m s t PaperAESOverlapResources.entry
        PaperAESOverlapResources.delta PaperAESOverlapResources.total := by
  rw [physical_overlap_norm_eq CL CR s t hCL hCR hs ht]
  exact PaperAESOverlapHS.equal_bits_norm_of_entry _ _ hs ht adjoint bit hentry

end AES8.PaperAESOverlapShortening
