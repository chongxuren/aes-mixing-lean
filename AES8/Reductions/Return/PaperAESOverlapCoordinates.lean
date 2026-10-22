import AES8.Reductions.Return.PaperAESIncidence
import AES8.Reductions.Return.PaperAESOverlapBound
import AES8.Math.PaperKernelReindex

/-! Coordinate equivalences between the literal incidence image and the affine
outside labels used by the normalized overlap theorems. These preserve original
coordinates, including zero-dimensional outside spaces; no MDS hypothesis is
needed for reindexing. Norm estimates and physical return assembly are separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESOverlapCoordinates
open AESMixing PaperMDSOverlap PaperGraphResponseMatrix PaperAESIncidence

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {I M V : Type*} [Fintype I] [Fintype M] [Fintype V]
  [DecidableEq I] [DecidableEq M] [DecidableEq V] [AddCommGroup V]

def zeroCodeEquiv (C : AddSubgroup ((I ⊕ M) → V)) : C ≃ AffineCode C 0 :=
  (affineCodeEquiv C 0).symm

@[simp] theorem zeroCodeEquiv_val (C : AddSubgroup ((I ⊕ M) → V)) (c : C) :
    (zeroCodeEquiv C c).val = c.val := by
  simp [zeroCodeEquiv, affineCodeEquiv]

def leftEquiv : I ≃ (leftPositions (I := I) (M := M)) where
  toFun i := ⟨Sum.inl i, mem_leftPositions_inl i⟩
  invFun p := match h : p.val with
    | Sum.inl i => i
    | Sum.inr m => False.elim (not_mem_leftPositions_inr m (h ▸ p.property))
  left_inv i := rfl
  right_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl i => rfl
    | inr m => exact False.elim (not_mem_leftPositions_inr m hp)

@[simp] theorem leftEquiv_apply (i : I) :
    (leftEquiv (M := M) i).val = Sum.inl i := rfl

def outsideLabelToSet (C : AddSubgroup ((I ⊕ M) → V))
    (u : OutsideLabel C 0 (leftPositions (I := I) (M := M))) : outsideSet C :=
  ⟨fun i => u.val (leftEquiv i), by
    obtain ⟨x, hx⟩ := u.property
    apply (mem_outsideSet C _).mpr
    refine ⟨fun m => x.val (Sum.inr m), ?_⟩
    have hc : x.val ∈ C := by simpa only [sub_zero] using x.property
    convert hc using 1
    funext p
    cases p with
    | inl i => exact (congrFun hx (leftEquiv i)).symm
    | inr m => rfl⟩

def outsideSetToLabel (C : AddSubgroup ((I ⊕ M) → V)) (y : outsideSet C) :
    OutsideLabel C 0 (leftPositions (I := I) (M := M)) :=
  ⟨fun p => y.val (leftEquiv.symm p), by
    obtain ⟨x, hx⟩ := (mem_outsideSet C y.val).mp y.property
    refine ⟨zeroCodeEquiv C ⟨Sum.elim y.val x, hx⟩, ?_⟩
    funext p
    obtain ⟨i, rfl⟩ := leftEquiv.surjective p
    simp [outsideMap]⟩

def outsideLabelEquiv (C : AddSubgroup ((I ⊕ M) → V)) :
    outsideSet C ≃ OutsideLabel C 0 (leftPositions (I := I) (M := M)) where
  toFun := outsideSetToLabel C
  invFun := outsideLabelToSet C
  left_inv y := by
    apply Subtype.ext
    funext i
    simp [outsideLabelToSet, outsideSetToLabel]
  right_inv u := by
    apply Subtype.ext
    funext p
    simp [outsideLabelToSet, outsideSetToLabel]

@[simp] theorem outsideLabelEquiv_outside (C : AddSubgroup ((I ⊕ M) → V)) (c : C) :
    outsideLabelEquiv C (PaperAESIncidence.outside C c) =
      outsideProjection C 0 (leftPositions (I := I) (M := M)) (zeroCodeEquiv C c) := by
  apply Subtype.ext
  funext p
  obtain ⟨i, rfl⟩ := leftEquiv.surjective p
  simp [outsideLabelEquiv, outsideSetToLabel, outsideProjection,
    outsideMap, PaperAESIncidence.outside]

section TwoGraphs
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {𝕜 : Type*} [RCLike 𝕜]
open PaperFiberKernel PaperKernelBounds PaperKernelReindex

theorem compressed_middle_reindex
    (CL : AddSubgroup ((I ⊕ M) → V)) (CR : AddSubgroup ((J ⊕ M) → V))
    (T : M → V → V → 𝕜) (a b : ℕ) (y : outsideSet CL) (x : outsideSet CR) :
    compressedKernel (outside CL) (outside CR) a b
      (fun c d => ∏ m, T m (middle CL c m) (middle CR d m)) y x =
    compressedKernel
      (outsideProjection CL 0 (leftPositions (I := I) (M := M)))
      (outsideProjection CR 0 (leftPositions (I := J) (M := M))) a b
      (fun c d => ∏ m, T m (c.val (Sum.inr m)) (d.val (Sum.inr m)))
      (outsideLabelEquiv CL y) (outsideLabelEquiv CR x) := by
  apply compressedKernel_reindex (zeroCodeEquiv CL) (zeroCodeEquiv CR)
    (outsideLabelEquiv CL) (outsideLabelEquiv CR)
  · intro c; exact (outsideLabelEquiv_outside CL c).symm
  · intro c; exact (outsideLabelEquiv_outside CR c).symm
  · intro c d
    simp only [zeroCodeEquiv_val, middle]

theorem normalized_middle_norm_eq
    (CL : AddSubgroup ((I ⊕ M) → V)) (CR : AddSubgroup ((J ⊕ M) → V))
    (T : M → V → V → 𝕜) (a b : ℕ) :
    ‖kernelOperator (compressedKernel (outside CL) (outside CR) a b
      (fun c d => ∏ m, T m (middle CL c m) (middle CR d m)))‖ =
    ‖kernelOperator (compressedKernel
      (outsideProjection CL 0 (leftPositions (I := I) (M := M)))
      (outsideProjection CR 0 (leftPositions (I := J) (M := M))) a b
      (fun c d => ∏ m, T m (c.val (Sum.inr m)) (d.val (Sum.inr m))))‖ := by
  have he := funext fun y => funext fun x => compressed_middle_reindex CL CR T a b y x
  rw [he]
  exact kernelOperator_reindex (outsideLabelEquiv CR) (outsideLabelEquiv CL) _

end TwoGraphs

/-- The incidence code spaces and the physical normalized overlap have
exactly the same operator norm; all fiber normalizers stay inside the matrix. -/
theorem aes_overlap_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (adjoint eL eR : Bool) :
    ‖PaperKernelBounds.kernelOperator
      (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
        (PaperAESOverlapResources.q ^ (s - min s i))
        (PaperAESOverlapResources.q ^ (t - min t j))
        (fun c d => ((∏ k, PaperWordMixedGram.mixed adjoint eL eR
          (middle CL c k) (middle CR d k) : ℝ) : ℂ)))‖ =
    ‖PaperAESOverlapLarge.overlap CL CR s t 0 0
      (⟨Sum.inr, Sum.inr_injective⟩ : Fin m ↪ Fin i ⊕ Fin m)
      (⟨Sum.inr, Sum.inr_injective⟩ : Fin m ↪ Fin j ⊕ Fin m)
      (leftPositions (I := Fin i) (M := Fin m))
      (leftPositions (I := Fin j) (M := Fin m)) adjoint eL eR‖ := by
  simp only [Complex.ofReal_prod]
  rw [normalized_middle_norm_eq CL CR
    (fun _ y x => (PaperWordMixedGram.mixed adjoint eL eR y x : ℂ))
    (PaperAESOverlapResources.q ^ (s - min s i))
    (PaperAESOverlapResources.q ^ (t - min t j))]
  rw [PaperAESOverlapLarge.overlap, ← PaperFiberKernel.compression_eq_adjoint_comp]
  simp only [leftPositions_card, Fintype.card_fin,
    PaperPhysicalOverlap.physicalMiddleKernel, Complex.ofReal_prod]
  rfl

/-- Transfer a complex normalized-overlap cap to the real incidence matrix.
This does not alter or omit the square-root fiber normalizers. -/
theorem aes_real_overlap_norm_le {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (adjoint eL eR : Bool) :
    ‖PaperKernelBounds.kernelOperator
      (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
        (PaperAESOverlapResources.q ^ (s - min s i))
        (PaperAESOverlapResources.q ^ (t - min t j))
        (fun c d => ∏ k, PaperWordMixedGram.mixed adjoint eL eR
          (middle CL c k) (middle CR d k)))‖ ≤
    ‖PaperAESOverlapLarge.overlap CL CR s t 0 0
      (⟨Sum.inr, Sum.inr_injective⟩ : Fin m ↪ Fin i ⊕ Fin m)
      (⟨Sum.inr, Sum.inr_injective⟩ : Fin m ↪ Fin j ⊕ Fin m)
      (leftPositions (I := Fin i) (M := Fin m))
      (leftPositions (I := Fin j) (M := Fin m)) adjoint eL eR‖ := by
  have h := PaperKernelReindex.real_kernel_norm_le_complex
    (PaperFiberKernel.compressedKernel (outside CL) (outside CR)
      (PaperAESOverlapResources.q ^ (s - min s i))
      (PaperAESOverlapResources.q ^ (t - min t j))
      (fun c d => ∏ k, PaperWordMixedGram.mixed adjoint eL eR
        (middle CL c k) (middle CR d k)))
  rw [← PaperAESOverlapBound.compressedKernel_complexification,
    aes_overlap_norm CL CR s t adjoint eL eR] at h
  exact h

end AES8.PaperAESOverlapCoordinates
