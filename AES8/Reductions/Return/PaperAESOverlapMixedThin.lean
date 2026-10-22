import AES8.Reductions.Return.PaperAESOverlapThin
import AES8.Estimates.Word.PaperExceptionalWordFourth

/-!
# Unequal-Fourier AES thin overlaps from concrete fourth moments

Frozen paper f902bb94, `eq:aesasm-moment-choice`, `eq:aesasm-overlap-lines`
and `eq:aesasm-overlap-line-plane`. The side flag enumerates exactly the
two unequal Fourier choices; the adjoint flag is independent. Concrete
exceptional-word fourth moments supply 2100/q and 1200/q, while the current
second moments supply the barred row and total resources. Both physical
fiber maps and all coordinate inclusions remain inside the literal complex
operators. No simultaneous-Fourier 27/q entry cap is asserted here.
Constructive proof checking only; no attacks, searches or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapMixedThin
open AESMixing AESConcrete PaperMDSShortening PaperThinLines PaperThinPlaneShort
open PaperFiberKernel PaperKernelBounds PaperAESOverlapResources

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {K J : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

def rowFourthBase : ℝ := 2100 / q
def totalFourthBase : ℝ := 1200 / q

theorem rowFourthBase_nonneg : 0 ≤ rowFourthBase := by norm_num [rowFourthBase, q]
theorem totalFourthBase_nonneg : 0 ≤ totalFourthBase := by norm_num [totalFourthBase, q]

/-- Side=false is right Fourier only; side=true is left Fourier only. -/
def oneSided (n : ℕ) (adjoint side : Bool) : Fin n → AES.Word → AES.Word → ℂ :=
  fun _ y x => (PaperWordMixedGram.mixed adjoint side (!side) y x : ℂ)

/-- Literal transpose bridge for the left-only Fourier choice. -/
theorem left_only_transpose (adjoint : Bool) (y x : AES.Word) :
    PaperWordMixedGram.mixed adjoint true false y x =
      OneSidedWordEnergy.rightMixed (!adjoint) x y := by
  unfold PaperWordMixedGram.mixed OneSidedWordEnergy.rightMixed kernelCompose
  simp only [Bool.false_eq_true, if_false, if_true,
    OneSidedWordEnergy.baseResidual_transpose]
  apply Finset.sum_congr rfl
  intro z _
  rw [WordFourierCore.wordFourier_symmetric y z]
  ring

theorem oneSided_row_fourth_lt (adjoint side : Bool) (y : AES.Word) :
    (∑ x, PaperWordMixedGram.mixed adjoint side (!side) y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  cases side
  · exact PaperExceptionalWordFourth.row_fourth_lt adjoint y
  · simp only [Bool.not_true]
    simp_rw [left_only_transpose]
    exact PaperExceptionalWordFourth.column_fourth_lt (!adjoint) y

theorem oneSided_column_fourth_lt (adjoint side : Bool) (x : AES.Word) :
    (∑ y, PaperWordMixedGram.mixed adjoint side (!side) y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  cases side
  · exact PaperExceptionalWordFourth.column_fourth_lt adjoint x
  · simp only [Bool.not_true]
    simp_rw [left_only_transpose]
    exact PaperExceptionalWordFourth.row_fourth_lt (!adjoint) x

theorem oneSided_total_fourth_lt (adjoint side : Bool) :
    (∑ y, ∑ x, PaperWordMixedGram.mixed adjoint side (!side) y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) := by
  cases side
  · exact PaperExceptionalWordFourth.total_fourth_lt adjoint
  · simp only [Bool.not_true]
    simp_rw [left_only_transpose]
    rw [Finset.sum_comm]
    exact PaperExceptionalWordFourth.total_fourth_lt (!adjoint)

/-- All four actual unequal-bit kernels meet the printed complex moment
interface; no exceptional-entry or exceptional-sum hypothesis remains. -/
theorem oneSided_moments (n : ℕ) (adjoint side : Bool) :
    EntryMoments (oneSided n adjoint side) delta total rowFourthBase totalFourthBase := by
  have hfourth (r : ℝ) : ‖(r : ℂ)‖ ^ 4 = r ^ 4 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, show 4 = 2 * 2 from rfl,
      pow_mul, sq_abs]
  refine ⟨delta_nonneg, total_nonneg, rowFourthBase_nonneg, totalFourthBase_nonneg,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ y
    simpa only [oneSided, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      mixed_row_energy adjoint side (!side) y
  · intro _ x
    simpa only [oneSided, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      mixed_column_energy adjoint side (!side) x
  · intro _
    simpa only [oneSided, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      mixed_total_energy adjoint side (!side)
  · intro _ y
    have h := (oneSided_row_fourth_lt adjoint side y).le.trans
      (show (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) ≤
        rowFourthBase ^ 2 * delta by norm_num [rowFourthBase, delta, q])
    simpa only [oneSided, hfourth] using h
  · intro _ x
    have h := (oneSided_column_fourth_lt adjoint side x).le.trans
      (show (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) ≤
        rowFourthBase ^ 2 * delta by norm_num [rowFourthBase, delta, q])
    simpa only [oneSided, hfourth] using h
  · intro _
    have h := (oneSided_total_fourth_lt adjoint side).le.trans
      (show (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) ≤
        totalFourthBase ^ 2 * total by norm_num [totalFourthBase, total, q])
    simpa only [oneSided, hfourth] using h

def lineCap (n a : ℕ) : ℝ :=
  if a = 0 then delta * rowFourthBase ^ (n - 2)
    else total * totalFourthBase ^ (n - 2)

def twoLines {n : ℕ} (L : PhysicalShortening K AES.Word 1 n)
    (R : PhysicalShortening J AES.Word 1 n) (adjoint side : Bool) :
    EuclideanSpace ℂ R.Labels →L[ℂ] EuclideanSpace ℂ L.Labels :=
  normalizedLineOverlap (oneSided n adjoint side) (fun x : L.Points => x.val)
    (fun y : R.Points => y.val) L.middle R.middle L.observed R.observed

/-- The printed two-line quotient for both unequal Fourier choices and
both adjoints, for every outside fiber on larger physical affine graphs. -/
theorem twoLines_norm {n : ℕ} (hn : n = 3 ∨ n = 4)
    (L : PhysicalShortening K AES.Word 1 n) (R : PhysicalShortening J AES.Word 1 n)
    (adjoint side : Bool) :
    ‖twoLines L R adjoint side‖ ≤
      Real.sqrt (lineCap n L.fiberDimension * lineCap n R.fiberDimension /
        (q : ℝ) ^ (L.fiberDimension + R.fiberDimension)) := by
  have h := (paper_affine_two_lines n hn L.code R.code L.dimension R.dimension
    L.dimension_le R.dimension_le L.mds R.mds L.offset R.offset L.fixed R.fixed
    L.target R.target L.remaining R.remaining L.middle R.middle
    L.middle_unfixed R.middle_unfixed L.observed R.observed L.outside_unfixed.symm
    R.outside_unfixed.symm L.middle_outside R.middle_outside (oneSided n adjoint side)
    delta total rowFourthBase totalFourthBase (oneSided_moments n adjoint side)).2.2
  calc
    ‖twoLines L R adjoint side‖ ≤
        Real.sqrt ((partialCap L.observed (delta * rowFourthBase ^ (n - 2))
          (total * totalFourthBase ^ (n - 2)) *
          partialCap R.observed (delta * rowFourthBase ^ (n - 2))
            (total * totalFourthBase ^ (n - 2))) /
              (Fintype.card AES.Word : ℝ) ^
                (outsideDimension L.observed + outsideDimension R.observed)) := h
    _ = _ := by
      rw [partialCap_dimension, partialCap_dimension,
        ← PaperAESOverlapThin.line_fiberDimension n L,
        ← PaperAESOverlapThin.line_fiberDimension n R, WordFourierCore.word_card]
      rfl

def linePlane (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint side : Bool) :
    EuclideanSpace ℂ P.Labels →L[ℂ] EuclideanSpace ℂ L.Labels :=
  (fiberLift L.projection (q ^ L.fiberDimension)).adjoint.comp
    (((coordinateInclusion (middle L)).adjoint.comp
      ((coordinateTensorOperator (oneSided 4 adjoint side)).comp
        (coordinateInclusion (middle P)))).comp
          (fiberLift P.projection (q ^ P.fiberDimension)))

/-- All six printed line/plane fiber cases, with the actual complex tensor
compression and concrete one-sided fourth-moment resources. -/
theorem linePlane_norm (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint side : Bool) :
    ‖linePlane L P adjoint side‖ ≤
      Real.sqrt ((delta ^ (2 - L.fiberDimension) * total ^ L.fiberDimension *
        PaperThinPlane.planeColCap P.fiberDimension delta total rowFourthBase totalFourthBase) /
          (q : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  have h := paper_affine_line_plane_tensor L P (oneSided 4 adjoint side)
    delta total rowFourthBase totalFourthBase (oneSided_moments 4 adjoint side)
  simpa only [linePlane, PaperThinPlane.planeRowCap, WordFourierCore.word_card, q] using h

/-- Plane on the left is the literal Hilbert adjoint, so both fiber maps
and all coordinate inclusions are exchanged by the actual operator. -/
theorem planeLine_norm (L : Line (K := K) (V := AES.Word))
    (P : Plane (J := J) (V := AES.Word)) (adjoint side : Bool) :
    ‖(linePlane L P adjoint side).adjoint‖ ≤
      Real.sqrt ((delta ^ (2 - L.fiberDimension) * total ^ L.fiberDimension *
        PaperThinPlane.planeColCap P.fiberDimension delta total rowFourthBase totalFourthBase) /
          (q : ℝ) ^ (L.fiberDimension + P.fiberDimension)) := by
  rw [LinearIsometryEquiv.norm_map]
  exact linePlane_norm L P adjoint side

end AES8.PaperAESOverlapMixedThin
