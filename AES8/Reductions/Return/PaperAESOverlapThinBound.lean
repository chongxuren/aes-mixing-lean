import AES8.Math.PaperEntryMoments
import AES8.Reductions.Return.PaperAESOverlapShortening
import AES8.Recurrence.PaperThinComparisonBridge

/-! Literal thin overlap menu on incidence code types. The shared moment
interface supplies all four shapes. Equal-true retains its exact pointwise
27/q resource; ordinary and unequal choices discharge their own resources. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESOverlapThinBound
open AESMixing PaperMDSGram PaperMDSShortening PaperThinLines PaperThinPlaneShort
open PaperFiberKernel PaperKernelBounds PaperAESOverlapResources PaperThinComparisonBridge
open PaperAESOverlapShortening
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {K J : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

/-- Only the unresolved simultaneous-Fourier case requires a premise. -/
def EntryResource (adjoint eL eR : Bool) : Prop :=
  eL = true ∧ eR = true →
    ∀ y x, |PaperWordMixedGram.mixed adjoint eL eR y x| ≤ entry

theorem entryResource_ordinary (adjoint : Bool) : EntryResource adjoint false false := by
  intro h
  cases h.1

theorem entryResource_oneSided (adjoint side : Bool) : EntryResource adjoint side (!side) := by
  cases side <;> simp [EntryResource]

/-- Transposition reverses the independent Fourier choices and the residual
orientation. This identity records the bits used by the plane-left adjoint. -/
theorem mixed_transpose (adjoint eL eR : Bool) (y x : AES.Word) :
    PaperWordMixedGram.mixed (!adjoint) eR eL y x =
      PaperWordMixedGram.mixed adjoint eL eR x y := by
  cases eL <;> cases eR
  · exact OneSidedWordEnergy.baseResidual_transpose adjoint y x
  · change PaperWordMixedGram.mixed (!adjoint) true false y x =
      OneSidedWordEnergy.rightMixed adjoint x y
    simpa only [Bool.not_not] using
      PaperAESOverlapMixedThin.left_only_transpose (!adjoint) y x
  · exact (PaperAESOverlapMixedThin.left_only_transpose adjoint x y).symm
  · have ht : AESConcrete.WordFourierVariants.baseResidual (!adjoint) =
        fun y x => AESConcrete.WordFourierVariants.baseResidual adjoint x y := by
      funext a b
      exact OneSidedWordEnergy.baseResidual_transpose adjoint a b
    change AESConcrete.WordFourierCore.wordConjugate
        (AESConcrete.WordFourierVariants.baseResidual (!adjoint)) y x =
      AESConcrete.WordFourierCore.wordConjugate
        (AESConcrete.WordFourierVariants.baseResidual adjoint) x y
    rw [ht, PaperWordMixedGram.wordConjugate_transpose]

theorem mixed_conjTranspose (adjoint eL eR : Bool) :
    Matrix.conjTranspose (fun y x => (PaperWordMixedGram.mixed adjoint eL eR y x : ℂ)) =
      fun y x => (PaperWordMixedGram.mixed (!adjoint) eR eL y x : ℂ) := by
  ext y x
  change (starRingEnd ℂ) (PaperWordMixedGram.mixed adjoint eL eR x y : ℂ) = _
  rw [mixed_transpose]
  exact Complex.conj_ofReal _

theorem moments (n : ℕ) (adjoint eL eR : Bool)
    (hentry : EntryResource adjoint eL eR) :
    EntryMoments (fun _ : Fin n => fun y x =>
      (PaperWordMixedGram.mixed adjoint eL eR y x : ℂ))
      delta total (rowScale (eL == eR)) (totalScale (eL == eR)) := by
  cases eL <;> cases eR
  · exact PaperAESOverlapThin.ordinary_moments n adjoint
  · exact PaperAESOverlapMixedThin.oneSided_moments n adjoint false
  · exact PaperAESOverlapMixedThin.oneSided_moments n adjoint true
  · apply PaperEntryMoments.of_entry _ delta total entry
      delta_nonneg total_nonneg entry_nonneg
    · intro _ y x
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hentry ⟨rfl, rfl⟩ y x
    · intro _ y
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        mixed_row_energy adjoint true true y
    · intro _ x
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        mixed_column_energy adjoint true true x
    · intro _
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        mixed_total_energy adjoint true true

theorem line_norm {n : ℕ} (hn : n = 3 ∨ n = 4)
    (L : PhysicalShortening K AES.Word 1 n) (R : PhysicalShortening J AES.Word 1 n)
    (T : Fin n → AES.Word → AES.Word → ℝ) (same : Bool)
    (hm : EntryMoments (fun j y x => (T j y x : ℂ)) delta total
      (rowScale same) (totalScale same)) :
    ‖PaperAESOverlapHS.normalizedOverlap L R T‖ ≤
      twoLineCoefficient n L.fiberDimension R.fiberDimension same := by
  have h := (paper_affine_two_lines n hn L.code R.code L.dimension R.dimension
    L.dimension_le R.dimension_le L.mds R.mds L.offset R.offset L.fixed R.fixed
    L.target R.target L.remaining R.remaining L.middle R.middle
    L.middle_unfixed R.middle_unfixed L.observed R.observed L.outside_unfixed.symm
    R.outside_unfixed.symm L.middle_outside R.middle_outside
    (fun j y x => (T j y x : ℂ)) delta total (rowScale same) (totalScale same) hm).2.2
  have he : PaperAESOverlapHS.normalizedOverlap L R T =
      normalizedLineOverlap (fun j y x => (T j y x : ℂ))
        (fun x : L.Points => x.val) (fun x : R.Points => x.val)
        L.middle R.middle L.observed R.observed := by
    unfold normalizedLineOverlap
    rw [normalized_overlap_correspondence]
    rw [← PaperAESOverlapThin.line_fiberDimension n L,
      ← PaperAESOverlapThin.line_fiberDimension n R]
    simp only [PaperAESOverlapHS.normalizedOverlap, PaperAESOverlapHS.rawKernel,
      PaperAESOverlapHS.shortMiddle, Complex.ofReal_prod]
    rfl
  rw [he]
  apply h.trans_eq
  rw [partialCap_dimension, partialCap_dimension,
    ← PaperAESOverlapThin.line_fiberDimension n L,
    ← PaperAESOverlapThin.line_fiberDimension n R,
    AESConcrete.WordFourierCore.word_card]
  rfl

theorem line_plane_norm (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word))
    (T : Fin 4 → AES.Word → AES.Word → ℝ) (same : Bool)
    (hm : EntryMoments (fun j y x => (T j y x : ℂ)) delta total
      (rowScale same) (totalScale same)) :
    ‖PaperAESOverlapHS.normalizedOverlap L P T‖ ≤
      linePlaneCoefficient L.fiberDimension P.fiberDimension same := by
  have h := paper_affine_line_plane_tensor L P (fun j y x => (T j y x : ℂ))
    delta total (rowScale same) (totalScale same) hm
  have he : PaperAESOverlapHS.normalizedOverlap L P T =
      (fiberLift L.projection (Fintype.card AES.Word ^ L.fiberDimension)).adjoint.comp
        (((coordinateInclusion (PaperThinPlaneShort.middle L)).adjoint.comp
          ((coordinateTensorOperator (fun j y x => (T j y x : ℂ))).comp
            (coordinateInclusion (PaperThinPlaneShort.middle P)))).comp
              (fiberLift P.projection (Fintype.card AES.Word ^ P.fiberDimension))) := by
    rw [normalized_overlap_correspondence]
    simp only [PaperAESOverlapHS.normalizedOverlap, PaperAESOverlapHS.rawKernel,
      PaperAESOverlapHS.shortMiddle,
      Complex.ofReal_prod, AESConcrete.WordFourierCore.word_card]
    rfl
  rw [he]
  simpa only [linePlaneCoefficient, PaperThinPlane.planeRowCap,
    AESConcrete.WordFourierCore.word_card, q] using h

/-- The plane-left estimate is applied to the conjugate-transposed local
matrix. The actual Hilbert adjoint exchanges both outside fiber maps. -/
theorem plane_line_norm (P : Plane (J := K) (V := AES.Word))
    (L : Line (K := J) (V := AES.Word))
    (T : Fin 4 → AES.Word → AES.Word → ℝ) (same : Bool)
    (hm : EntryMoments (fun j y x => (T j y x : ℂ)) delta total
      (rowScale same) (totalScale same)) :
    ‖PaperAESOverlapHS.normalizedOverlap P L T‖ ≤
      linePlaneCoefficient L.fiberDimension P.fiberDimension same := by
  have hm' := PaperEntryMoments.conjTranspose _ _ _ _ _ hm
  have h := paper_affine_line_plane_adjoint L P
    (fun j => Matrix.conjTranspose (fun y x => (T j y x : ℂ)))
    delta total (rowScale same) (totalScale same) hm'
  have he : Matrix.conjTranspose
      (lineKernel (fun j => Matrix.conjTranspose (fun y x => (T j y x : ℂ)))
        (PaperThinPlaneShort.middle L) (PaperThinPlaneShort.middle P)) =
      (fun y x => (PaperAESOverlapHS.rawKernel T
        (PaperAESOverlapHS.shortMiddle P) (PaperAESOverlapHS.shortMiddle L) y x : ℂ)) := by
    ext y x
    simp only [Matrix.conjTranspose_apply, lineKernel, star_prod, star_star,
      PaperAESOverlapHS.rawKernel, PaperAESOverlapHS.shortMiddle,
      PaperThinPlaneShort.middle, Complex.ofReal_prod]
  rw [he] at h
  simpa only [PaperAESOverlapHS.normalizedOverlap, linePlaneCoefficient,
    PaperThinPlane.planeRowCap, AESConcrete.WordFourierCore.word_card, q] using h

theorem shortening_thin_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (hshape : ThinShape m s t) (adjoint eL eR : Bool)
    (hentry : EntryResource adjoint eL eR) :
    ‖PaperAESOverlapHS.normalizedOverlap (shortening CL s hCL hs)
      (shortening CR t hCR ht) (fun _ => PaperWordMixedGram.mixed adjoint eL eR)‖ ≤
      thinCoefficient m s t (s-min s i) (t-min t j) (eL == eR) := by
  have hm := moments m adjoint eL eR hentry
  rcases hshape with ⟨rfl, rfl, hc⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simpa only [shortening_fiberDimension, thinCoefficient, and_self,
      if_true] using line_norm hc (shortening CL 1 hCL hs) (shortening CR 1 hCR ht)
        _ (eL == eR) hm
  · simpa [thinCoefficient] using
      line_plane_norm (shortening CL 1 hCL hs) (shortening CR 2 hCR ht) _ (eL == eR) hm
  · simpa [thinCoefficient] using
      plane_line_norm (shortening CL 2 hCL hs) (shortening CR 1 hCR ht) _ (eL == eR) hm

theorem physical_overlap_thin_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ)
    (hCL : IsMDS CL s) (hCR : IsMDS CR t) (hs : s ≤ m) (ht : t ≤ m)
    (hshape : ThinShape m s t) (adjoint eL eR : Bool)
    (hentry : EntryResource adjoint eL eR) :
    ‖PaperAESOverlapLarge.overlap CL CR s t 0 0
      (PaperAESOverlapBound.middleEmbedding (Fin i) (Fin m))
      (PaperAESOverlapBound.middleEmbedding (Fin j) (Fin m))
      (PaperGraphResponseMatrix.leftPositions (I := Fin i) (M := Fin m))
      (PaperGraphResponseMatrix.leftPositions (I := Fin j) (M := Fin m)) adjoint eL eR‖ ≤
      thinCoefficient m s t (s-min s i) (t-min t j) (eL == eR) := by
  rw [physical_overlap_norm_eq CL CR s t hCL hCR hs ht]
  exact shortening_thin_norm CL CR s t hCL hCR hs ht hshape adjoint eL eR hentry

end AES8.PaperAESOverlapThinBound
