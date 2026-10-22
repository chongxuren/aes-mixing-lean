import AES8.Reductions.Return.PaperAESOverlapResources
import AES8.Math.PaperThinPlaneShort

/-!
# Unconditional ordinary AES thin-code overlap choices

Frozen paper f902bb94, equations `aesasm-overlap-lines` and
`aesasm-overlap-line-plane`, with both Fourier bits zero. The actual
27/q entry cap supplies fourth moments; current source columns and their
transposes supply second moments. The generic physical affine-shortening
theorems derive every fiber, normalization and coordinate inclusion.
The resulting operators act on arbitrary complex inputs.

The other same-bit choice still needs its sharper simultaneous-Fourier
entry resource, and the unequal-bit choices need their actual one-sided
fourth moments. Neither unresolved resource is asserted here.
Constructive proof checking only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapThin
open AESMixing AESConcrete PaperMDSShortening PaperThinLines PaperThinPlaneShort
open PaperFiberKernel PaperKernelBounds PaperAESOverlapResources

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {K J : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

def ordinary (n : ℕ) (adjoint : Bool) : Fin n → AES.Word → AES.Word → ℂ :=
  fun _ y x => (PaperWordMixedGram.mixed adjoint false false y x : ℂ)

theorem ordinary_moments (n : ℕ) (adjoint : Bool) :
    EntryMoments (ordinary n adjoint) delta total entry entry := by
  have h := ordinary_entry_moments n adjoint
  refine ⟨h.delta_nonneg, h.tau_nonneg, h.rowScale_nonneg, h.totalScale_nonneg,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j y
    simpa only [ordinary, Complex.norm_real] using h.row_second j y
  · intro j x
    simpa only [ordinary, Complex.norm_real] using h.col_second j x
  · intro j
    simpa only [ordinary, Complex.norm_real] using h.total_second j
  · intro j y
    simpa only [ordinary, Complex.norm_real] using h.row_fourth j y
  · intro j x
    simpa only [ordinary, Complex.norm_real] using h.col_fourth j x
  · intro j
    simpa only [ordinary, Complex.norm_real] using h.total_fourth j

def lineCap (n a : ℕ) : ℝ :=
  if a = 0 then delta * entry ^ (n - 2) else total * entry ^ (n - 2)

theorem line_fiberDimension (n : ℕ) (L : PhysicalShortening K AES.Word 1 n) :
    L.fiberDimension = outsideDimension L.observed := by
  by_cases h : L.observed = ∅
  · simp [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
      outsideDimension, h]
  · have hp : 1 ≤ L.observed.card :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    simp [PhysicalShortening.fiberDimension, PhysicalShortening.outsideRank,
      outsideDimension, h, Nat.min_eq_left hp]

def twoLines {n : ℕ} (L : PhysicalShortening K AES.Word 1 n)
    (R : PhysicalShortening J AES.Word 1 n) (adjoint : Bool) :
    EuclideanSpace ℂ R.Labels →L[ℂ] EuclideanSpace ℂ L.Labels :=
  normalizedLineOverlap (ordinary n adjoint) (fun x : L.Points => x.val)
    (fun y : R.Points => y.val) L.middle R.middle L.observed R.observed

/-- The printed two-line quotient for every physical outside fiber. -/
theorem twoLines_norm {n : ℕ} (hn : n = 3 ∨ n = 4)
    (L : PhysicalShortening K AES.Word 1 n) (R : PhysicalShortening J AES.Word 1 n)
    (adjoint : Bool) :
    ‖twoLines L R adjoint‖ ≤
      Real.sqrt (lineCap n L.fiberDimension * lineCap n R.fiberDimension /
        (q : ℝ) ^ (L.fiberDimension + R.fiberDimension)) := by
  have h := (paper_affine_two_lines n hn L.code R.code L.dimension R.dimension
    L.dimension_le R.dimension_le L.mds R.mds L.offset R.offset L.fixed R.fixed
    L.target R.target L.remaining R.remaining L.middle R.middle
    L.middle_unfixed R.middle_unfixed L.observed R.observed L.outside_unfixed.symm
    R.outside_unfixed.symm L.middle_outside R.middle_outside (ordinary n adjoint)
    delta total entry entry (ordinary_moments n adjoint)).2.2
  calc
    ‖twoLines L R adjoint‖ ≤
        Real.sqrt ((partialCap L.observed (delta * entry ^ (n - 2))
          (total * entry ^ (n - 2)) *
          partialCap R.observed (delta * entry ^ (n - 2)) (total * entry ^ (n - 2))) /
            (Fintype.card AES.Word : ℝ) ^
              (outsideDimension L.observed + outsideDimension R.observed)) := h
    _ = _ := by
      rw [partialCap_dimension, partialCap_dimension, ← line_fiberDimension n L,
        ← line_fiberDimension n R, WordFourierCore.word_card]
      rfl

def linePlane (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint : Bool) :
    EuclideanSpace ℂ P.Labels →L[ℂ] EuclideanSpace ℂ L.Labels :=
  (fiberLift L.projection (q ^ L.fiberDimension)).adjoint.comp
    (((coordinateInclusion (middle L)).adjoint.comp
      ((coordinateTensorOperator (ordinary 4 adjoint)).comp
        (coordinateInclusion (middle P)))).comp
          (fiberLift P.projection (q ^ P.fiberDimension)))

/-- All six line/plane cases on arbitrary larger physical affine shortenings. -/
theorem linePlane_norm (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint : Bool) :
    ‖linePlane L P adjoint‖ ≤
      Real.sqrt ((delta ^ (2 - L.fiberDimension) * total ^ L.fiberDimension *
        PaperThinPlane.planeColCap P.fiberDimension delta total entry entry) /
          (q : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  have h := paper_affine_line_plane_tensor L P (ordinary 4 adjoint)
    delta total entry entry (ordinary_moments 4 adjoint)
  simpa only [linePlane, PaperThinPlane.planeRowCap, WordFourierCore.word_card, q] using h

/-- Plane on the left is the actual Hilbert adjoint of the same operator. -/
theorem planeLine_norm (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint : Bool) :
    ‖(linePlane L P adjoint).adjoint‖ ≤
      Real.sqrt ((delta ^ (2 - L.fiberDimension) * total ^ L.fiberDimension *
        PaperThinPlane.planeColCap P.fiberDimension delta total entry entry) /
          (q : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  rw [LinearIsometryEquiv.norm_map]
  exact linePlane_norm L P adjoint

end AES8.PaperAESOverlapThin
