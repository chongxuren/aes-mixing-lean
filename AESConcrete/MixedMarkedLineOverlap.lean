import AESConcrete.MixedMarkedCoordinates
import AESConcrete.ShortenedByteLinearity
import AESConcrete.ShortenedLineBounds
import AESConcrete.FourierLineOverlap

/-!
# Actual line-pair overlaps on arbitrary mixed physical marked triples

The graph coordinates retain their input/output tags. Their field-linear
line slopes come from actual forward/inverse AES shortening. MDS equality
on mixed selected coordinates proves the ratio separation needed by the
existing independent-orientation analytic eta1/eta2 estimates. The zero-mask
intersection and union counts remain explicit finite geometry premises.
No plane-pair, signed aggregate or final degree-three bound is asserted.
Constructive mathematics only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedLineOverlap
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedByteLinearity
open AESConcrete.MixedMarkedCoordinates
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)

set_option maxRecDepth 100000

abbrev Byte := BinaryWord 8

def basisPoint (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) : ShortenedGraph (byteDiffusionHom inverse) r z :=
  (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z hshort (marked 0) (hm 0)).symm 1

theorem basis_coordinate (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    graphCoordinate (byteDiffusionHom inverse) (basisPoint inverse r z hshort marked hm).val (marked i) =
      lineCoefficient inverse r z hshort marked hm i := by
  exact (lineCoordinatePerm_apply (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z hshort marked hm i 1).symm

theorem basis_nonzero (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) :
    (basisPoint inverse r z hshort marked hm).val ≠ 0 := by
  have href : graphCoordinate (byteDiffusionHom inverse)
      (basisPoint inverse r z hshort marked hm).val (marked 0) = 1 := by
    have h := (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort (marked 0) (hm 0)).apply_symm_apply 1
    rw [coordinateEquiv_apply] at h
    exact h
  intro hzero
  rw [hzero, graphCoordinate_zero] at href
  exact zero_ne_one href

theorem scaled_basis_coordinate (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (c : Byte) (i : Fin 3) :
    graphCoordinate (byteDiffusionHom inverse)
      (scaleGraph inverse r z c (basisPoint inverse r z hshort marked hm)).val (marked i) =
      c * lineCoefficient inverse r z hshort marked hm i := by
  rw [graphCoordinate_scale, basis_coordinate]

theorem pair_equal_at_ratio (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (c : Byte) (i : Fin 3)
    (hc : c = lineCoefficient inverse r z hshort marked hm i /
      lineCoefficient inverse r' z' hshort' marked hm' i) :
    graphCoordinate (byteDiffusionHom inverse) (basisPoint inverse r z hshort marked hm).val (marked i) =
      graphCoordinate (byteDiffusionHom inverse)
        (scaleGraph inverse r' z' c (basisPoint inverse r' z' hshort' marked hm')).val (marked i) := by
  rw [basis_coordinate, scaled_basis_coordinate, hc]
  field_simp [lineCoefficient_ne_zero inverse r' z' hshort' marked hm' i]

/-- At least one shared physical zero and all three selected coordinates
identify the scaled graph points; their union zeros then force zero. -/
theorem ratios_nonconstant (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 1 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z')) :
    ¬ (lineCoefficient inverse r z hshort marked hm 0 /
          lineCoefficient inverse r' z' hshort' marked hm' 0 =
        lineCoefficient inverse r z hshort marked hm 1 /
          lineCoefficient inverse r' z' hshort' marked hm' 1 ∧
      lineCoefficient inverse r z hshort marked hm 1 /
          lineCoefficient inverse r' z' hshort' marked hm' 1 =
        lineCoefficient inverse r z hshort marked hm 2 /
          lineCoefficient inverse r' z' hshort' marked hm' 2) := by
  intro hr
  let c := lineCoefficient inverse r z hshort marked hm 0 /
    lineCoefficient inverse r' z' hshort' marked hm' 0
  let x := basisPoint inverse r z hshort marked hm
  let y := scaleGraph inverse r' z' c (basisPoint inverse r' z' hshort' marked hm')
  have hratio (i : Fin 3) : c = lineCoefficient inverse r z hshort marked hm i /
      lineCoefficient inverse r' z' hshort' marked hm' i := by
    fin_cases i
    · rfl
    · exact hr.1
    · exact hr.1.trans hr.2
  have hxy := selected_points_equal (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z r' z' marked hmarked (fun i => remaining_common r z r' z' (marked i) (hm i))
    (by simp only [Fintype.card_fin]; omega) x y
    (fun i => pair_equal_at_ratio inverse r z r' z' hshort hshort' marked hm hm' c i (hratio i))
  exact basis_nonzero inverse r z hshort marked hm
    (equal_points_zero_of_union (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z r' z' hunion x y hxy)

/-- With two shared physical zeros, any two equal ratios would already
identify the graph points. Thus all three ratios are pairwise distinct. -/
theorem ratios_injective (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 2 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z')) :
    Function.Injective (fun i => lineCoefficient inverse r z hshort marked hm i /
      lineCoefficient inverse r' z' hshort' marked hm' i) := by
  intro i j hij
  by_contra hne
  let selected : Fin 2 → GraphPosition := fun k => if k = 0 then marked i else marked j
  have hs : Function.Injective selected := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hne (hmarked (by simpa [selected] using hab))).elim
    · exact (hne (hmarked (by simpa [selected] using hab.symm))).elim
    · rfl
  have hf (k : Fin 2) : remaining (maskIntersection r r') (maskIntersection z z') (selected k) := by
    fin_cases k
    · simpa [selected] using remaining_common r z r' z' (marked i) (hm i)
    · simpa [selected] using remaining_common r z r' z' (marked j) (hm j)
  let c := lineCoefficient inverse r z hshort marked hm i /
    lineCoefficient inverse r' z' hshort' marked hm' i
  let x := basisPoint inverse r z hshort marked hm
  let y := scaleGraph inverse r' z' c (basisPoint inverse r' z' hshort' marked hm')
  have heq (k : Fin 2) : graphCoordinate (byteDiffusionHom inverse) x.val (selected k) =
      graphCoordinate (byteDiffusionHom inverse) y.val (selected k) := by
    fin_cases k
    · simpa [selected] using
        pair_equal_at_ratio inverse r z r' z' hshort hshort' marked hm hm' c i rfl
    · simpa [selected] using
        pair_equal_at_ratio inverse r z r' z' hshort hshort' marked hm hm' c j hij
  have hxy := selected_points_equal (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z r' z' selected hs hf (by simp only [Fintype.card_fin]; omega) x y heq
  exact basis_nonzero inverse r z hshort marked hm
    (equal_points_zero_of_union (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z r' z' hunion x y hxy)

theorem coordinatePerm_eq_slope (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) :
    lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z hshort marked hm =
      LineOverlap.slopeEquiv (lineCoefficient inverse r z hshort marked hm)
        (lineCoefficient_ne_zero inverse r z hshort marked hm) := by
  funext i
  exact lineCoordinatePerm_eq_mulLeft inverse r z hshort marked hm i

theorem normalizedResponse_eq_slope (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    ShortenedLineBounds.normalizedResponse inverse r z marked T y =
      DampedLineGram.lineResponse T
        (LineOverlap.slopeEquiv (lineCoefficient inverse r z hshort marked hm)
          (lineCoefficient_ne_zero inverse r z hshort marked hm)) y := by
  rw [ShortenedLineBounds.normalizedResponse_eq_line inverse r z hshort marked hm,
    coordinatePerm_eq_slope]

/-- Actual mixed-position eta2, with independently fixed actual
orientations and shared per-leg Fourier flags on both compared responses. -/
theorem actual_line_pair_eta2 (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 1 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z'))
    (o : Fin 3 → Orientation) (flags : Fin 3 → Bool) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      ShortenedLineBounds.normalizedResponse inverse r z marked (fun i => leg (o i) (flags i)) y *
      ShortenedLineBounds.normalizedResponse inverse r' z' marked (fun i => leg (o i) (flags i)) y| ≤
      LineOverlap.eta2 := by
  simp_rw [normalizedResponse_eq_slope inverse r z hshort marked hm,
    normalizedResponse_eq_slope inverse r' z' hshort' marked hm']
  exact FourierLineOverlap.actual_line_pair_eta2 o flags _ _
    (lineCoefficient_ne_zero inverse r z hshort marked hm)
    (lineCoefficient_ne_zero inverse r' z' hshort' marked hm')
    (ratios_nonconstant inverse r z r' z' hshort hshort' marked hmarked hm hm' hcommon hunion)

/-- Actual mixed-position eta1 under two shared physical zero constraints. -/
theorem actual_line_pair_eta1 (inverse : Bool) (r z r' z' : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (hshort' : maskSize r' + maskSize z' = 3)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : 2 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z'))
    (hunion : 4 ≤ maskSize (maskUnion r r') + maskSize (maskUnion z z'))
    (o : Fin 3 → Orientation) (flags : Fin 3 → Bool) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      ShortenedLineBounds.normalizedResponse inverse r z marked (fun i => leg (o i) (flags i)) y *
      ShortenedLineBounds.normalizedResponse inverse r' z' marked (fun i => leg (o i) (flags i)) y| ≤
      LineOverlap.eta1 := by
  simp_rw [normalizedResponse_eq_slope inverse r z hshort marked hm,
    normalizedResponse_eq_slope inverse r' z' hshort' marked hm']
  exact FourierLineOverlap.actual_line_pair_eta1 o flags _ _
    (lineCoefficient_ne_zero inverse r z hshort marked hm)
    (lineCoefficient_ne_zero inverse r' z' hshort' marked hm')
    (ratios_injective inverse r z r' z' hshort hshort' marked hmarked hm hm' hcommon hunion)

end AESConcrete.MixedMarkedLineOverlap
