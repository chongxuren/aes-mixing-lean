/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwelveConditionalResponse
import AES8.Reductions.Support.ZeroOutsideProjection

/-!
# The literal affine zero pin for incoming component eleven

Reuse the existing four `ZeroOutsideProjection.Q` patterns. Pointed channel
composition replaces one factor by the literal zero channel and the other
three by ordinary residuals. Conditioning factors only the original source
product law. Its zero channel selects exactly the inverse affine image of zero.
No current-boundary independence or numerical estimate is assumed.

Constructive proofs only; no attacks, manuscript or predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ElevenConditionalResponse
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)
open AESPaper.StartingWord (wordLaw sourceInput)
open AESPaper.GroupedLaw (groupedLaw error)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.TwelveConditionalResponse (support_project_tensorResponse
  conditionalTensorResponse tensorResponse_eq_probability_mixture)
open AES8.ZeroOutsideProjection (Q singleMask outsideMask)

def patternChannel (j i : Fin 4) : AES.Word → AES.Word → ℝ :=
  if i = j then zeroMatrix 0 else residualMatrix AES.wordSuperboxKernel 0

theorem pointed_pattern_left (j i : Fin 4) :
    kernelCompose
      (supportPiece (0 : AES.Word) (maskBit (outsideMask j) i) (maskBit (singleMask j) i))
      AES.wordSuperboxKernel = patternChannel j i := by
  by_cases hi : i = j
  · subst i
    have hm : maskBit (outsideMask j) j = false :=
      Bool.eq_false_iff.mpr (by simp [ZeroOutsideProjection.outsideMask_bit_iff])
    have hz : maskBit (singleMask j) j = true :=
      (ZeroOutsideProjection.singleMask_bit_iff j j).mpr rfl
    simpa [supportPiece, hm, hz, patternChannel] using
      (RefinedChannelCommutation.pointed_zero_left AES.word_superbox_pointed)
  · have hm : maskBit (outsideMask j) i = true :=
      (ZeroOutsideProjection.outsideMask_bit_iff j i).mpr hi
    have hz : maskBit (singleMask j) i = false :=
      Bool.eq_false_iff.mpr (fun h => hi ((ZeroOutsideProjection.singleMask_bit_iff j i).mp h))
    simpa [supportPiece, hm, hz, patternChannel, hi] using
      (FourResidualStep.pointed_residual_left AES.wordSuperboxKernel 0 AES.word_superbox_pointed)

theorem Q_law_eq_response (j : Fin 4) (b : AES.State) :
    Q j (groupedLaw 1 b) =
      tensorResponse (patternChannel j)
        (fun x : WordState => AESPaper.GroupedRecurrence.boundary x) (initialProduct b) := by
  rw [ZeroOutsideProjection.Q_eq_support_action,
    groupedLaw_one_eq_tensorResponse, support_project_tensorResponse]
  simp only [pointed_pattern_left]

def conditionalPattern (b : AES.State) (k : Fin 4) (w : OtherAssignments k)
    (j : Fin 4) : WordState → ℝ := conditionalTensorResponse (patternChannel j) b k w

def zeroPin (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) : AES.Word :=
  (affineEquiv k w j).symm 0

@[simp] theorem affine_zeroPin (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) :
    affineEquiv k w j (zeroPin k w j) = 0 := (affineEquiv k w j).apply_symm_apply 0

theorem affine_eq_zero_iff (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) (x : AES.Word) :
    affineEquiv k w j x = 0 ↔ x = zeroPin k w j := by
  constructor
  · intro h
    exact (affineEquiv k w j).injective (h.trans (affine_zeroPin k w j).symm)
  · rintro rfl
    exact affine_zeroPin k w j

def pinnedPattern (b : AES.State) (k : Fin 4) (w : OtherAssignments k)
    (j : Fin 4) (y : WordState) : ℝ :=
  if y j = 0 then wordLaw (sourceInput b k) (zeroPin k w j) *
    ∏ i : OtherCoordinates j,
      residualMatrix AES.wordSuperboxKernel 0 (y i.val)
        (affineEquiv k w i.val (zeroPin k w j)) else 0

/-- Collapse the literal zero channel before dropping any other restriction. -/
theorem conditionalPattern_eq_pinned (b : AES.State) (k : Fin 4)
    (w : OtherAssignments k) (j : Fin 4) :
    conditionalPattern b k w j = pinnedPattern b k w j := by
  funext y
  have hprod (x : AES.Word) :
      tensorColumn (patternChannel j) (fun x : AES.Word => fun i => affineEquiv k w i x) y x =
        zeroMatrix 0 (y j) (affineEquiv k w j x) *
          ∏ i : OtherCoordinates j,
            residualMatrix AES.wordSuperboxKernel 0 (y i.val) (affineEquiv k w i.val x) := by
    unfold tensorColumn
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [patternChannel, if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [i.property, if_false]
  unfold conditionalPattern conditionalTensorResponse tensorResponse
  simp_rw [hprod]
  have hpoint (x : AES.Word) :
      zeroMatrix 0 (y j) (affineEquiv k w j x) *
        (∏ i : OtherCoordinates j,
          residualMatrix AES.wordSuperboxKernel 0 (y i.val) (affineEquiv k w i.val x)) *
            wordLaw (sourceInput b k) x =
      if x = zeroPin k w j then
        (if y j = 0 then wordLaw (sourceInput b k) x *
          ∏ i : OtherCoordinates j,
            residualMatrix AES.wordSuperboxKernel 0 (y i.val) (affineEquiv k w i.val x) else 0)
      else 0 := by
    by_cases hx : x = zeroPin k w j
    · subst x
      by_cases hy : y j = 0 <;>
        simp only [zeroMatrix, identityKernel, affine_zeroPin, hy, ↓reduceIte,
          mul_one, one_mul, zero_mul, mul_zero] <;> ring
    · have he : affineEquiv k w j x ≠ 0 := (affine_eq_zero_iff k w j x).not.mpr hx
      simp only [zeroMatrix, identityKernel, hx, he, ↓reduceIte, mul_zero, zero_mul]
  simp_rw [hpoint]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, pinnedPattern]

/-- Remove the stationary reference at positive degree, then project and
condition the complete original source law. The sum is still signed. -/
theorem actual_component_eleven_eq_probability_mixture (b : AES.State) (k : Fin 4) :
    component (error 1 b) (11 : Fin 14) =
      fun y => ∑ w : OtherAssignments k, conditionWeight b k w *
        ∑ j : Fin 4, pinnedPattern b k w j y := by
  have href : component (error 1 b) (11 : Fin 14) = component (groupedLaw 1 b) (11 : Fin 14) := by
    change component (groupedLaw 1 b - uniformExcept (0 : WordState)) (11 : Fin 14) = _
    rw [OneSourceSupport.component_sub,
      OneSourceSupport.uniform_component_eq_zero (11 : Fin 14) (by decide), sub_zero]
  rw [href, ZeroOutsideProjection.component_eleven_eq_sum_Q]
  funext y
  have hpattern (j : Fin 4) : Q j (groupedLaw 1 b) y =
      ∑ w : OtherAssignments k, conditionWeight b k w * pinnedPattern b k w j y := by
    have h := congrFun ((Q_law_eq_response j b).trans
      (tensorResponse_eq_probability_mixture (patternChannel j) b k)) y
    change Q j (groupedLaw 1 b) y =
      ∑ w : OtherAssignments k, conditionWeight b k w * conditionalPattern b k w j y at h
    simpa only [conditionalPattern_eq_pinned] using h
  simp_rw [hpattern]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem residual_zero_row (x : AES.Word) :
    residualMatrix AES.wordSuperboxKernel 0 0 x = 0 := by
  simp only [residualMatrix, AES.word_superbox_pointed.zero_row, activityMatrix,
    if_true, sub_self]

/-- A second zero position forces one of the retained residual rows to zero. -/
theorem pinnedPattern_eq_zero_of_other_zero (b : AES.State) (k : Fin 4)
    (w : OtherAssignments k) (j i : Fin 4) (hij : i ≠ j)
    (y : WordState) (hy : y i = 0) : pinnedPattern b k w j y = 0 := by
  unfold pinnedPattern
  split_ifs
  · have hp : (∏ v : OtherCoordinates j,
        residualMatrix AES.wordSuperboxKernel 0 (y v.val)
          (affineEquiv k w v.val (zeroPin k w j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ ⟨i, hij⟩)
      rw [hy, residual_zero_row]
    rw [hp, mul_zero]
  · rfl

theorem pinnedPattern_pairwise (b : AES.State) (k : Fin 4)
    (w : OtherAssignments k) (y : WordState) (j i : Fin 4) (hji : j ≠ i) :
    pinnedPattern b k w j y * pinnedPattern b k w i y = 0 := by
  by_cases hy : y j = 0
  · rw [pinnedPattern_eq_zero_of_other_zero b k w i j hji y hy, mul_zero]
  · simp [pinnedPattern, hy]

/-- Disjointness is pointwise, so it survives any later fiber restriction. -/
theorem pinnedPattern_sum_sq (b : AES.State) (k : Fin 4)
    (w : OtherAssignments k) (y : WordState) :
    (∑ j : Fin 4, pinnedPattern b k w j y) ^ 2 =
      ∑ j : Fin 4, pinnedPattern b k w j y ^ 2 := by
  let F := fun j : Fin 4 => pinnedPattern b k w j y
  have h01 : F 0 * F 1 = 0 := pinnedPattern_pairwise b k w y 0 1 (by decide)
  have h02 : F 0 * F 2 = 0 := pinnedPattern_pairwise b k w y 0 2 (by decide)
  have h03 : F 0 * F 3 = 0 := pinnedPattern_pairwise b k w y 0 3 (by decide)
  have h12 : F 1 * F 2 = 0 := pinnedPattern_pairwise b k w y 1 2 (by decide)
  have h13 : F 1 * F 3 = 0 := pinnedPattern_pairwise b k w y 1 3 (by decide)
  have h23 : F 2 * F 3 = 0 := pinnedPattern_pairwise b k w y 2 3 (by decide)
  change (∑ j : Fin 4, F j) ^ 2 = ∑ j : Fin 4, F j ^ 2
  simp only [Fin.sum_univ_four]
  nlinarith

end AES8.ElevenConditionalResponse
