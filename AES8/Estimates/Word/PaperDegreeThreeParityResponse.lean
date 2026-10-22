import AES8.Estimates.Word.PaperDegreeThreeGramPrinted
import AES8.Math.PaperDegreeThreeParityCounts
import AESConcrete.DampedDegreeThree
import AES8.Math.PaperKernelBounds

/-! Actual same-parity response rows and cross-parity operator control.
The finite interval table is already derived from the physical damped responses.
This leaf partitions those actual entries, proves the 3/3 and 4/4 multiplicities,
and applies the signed rectangular Schur theorem. It does not assume row bounds
or a word norm as premises. Tensor metric lower bounds belong to a separate leaf.
Constructive proof work only; no attacks or canonical/vendor/manuscript edits. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParityResponse
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric
open AESConcrete.ActivityGramDominance
open AESConcrete.ActivityPairIntervals
open PaperDegreeThreeParityCounts
set_option autoImplicit false
set_option maxRecDepth 100000

def sizeInterval (w v j : ℕ) : ℝ × ℝ :=
  scaleInterval (4*frameFactor) (compressedInterval concreteResources w v j)
def responseRadius (w v j : ℕ) : ℝ :=
  max |(sizeInterval w v j).1| |(sizeInterval w v j).2|

theorem entry_abs_le_radius (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (A B : Interior) :
    |G A.val B.val| ≤ responseRadius (maskSize A.val) (maskSize B.val)
      (maskSize (maskIntersection A.val B.val)) := by
  rcases hG A B with ⟨hl, hu⟩
  change (sizeInterval _ _ _).1 ≤ _ at hl
  change _ ≤ (sizeInterval _ _ _).2 at hu
  unfold responseRadius
  apply abs_le.mpr
  have h0 := neg_abs_le (sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).1
  have h1 := le_abs_self (sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).2
  have hm0 := le_max_left |(sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).1|
    |(sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).2|
  have hm1 := le_max_right |(sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).1|
    |(sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).2|
  constructor <;> linarith

-- The numerical arithmetic is performed only for the three symbolic size rows.
theorem response_row_arithmetic :
    oddRow responseRadius 1 < (1024/255 : ℝ)*(9/8) ∧
    oddRow responseRadius 3 < (1024/255 : ℝ)*(9/8) ∧
    evenRow responseRadius 2 < (1024/255 : ℝ)*(229/100) := by
  norm_num [oddRow, evenRow, responseRadius, sizeInterval, scaleInterval,
    compressedInterval, concreteResources, frameFactor, ActivityPairIntervals.xi,
    ByteLineBounds.a3, ByteLineBounds.cubeBound, ByteGramResources.cubeNumerator,
    ByteLineBounds.b3, ByteLineBounds.mixedCubeBound, LineOverlap.eta1,
    LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag, MixedCodeBounds.f3,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3]

theorem odd_response_rows (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Odd) :
    (∑ B : Odd, |G A.val B.val|) < (1024/255 : ℝ)*(9/8) := by
  have h := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset Odd)) =>
    entry_abs_le_radius G hG ⟨A.val, odd_interior A⟩ ⟨B.val, odd_interior B⟩)
  rw [odd_row_classification responseRadius A.val (Or.inl A.property)] at h
  rcases A.property with hA | hA
  · rw [hA] at h
    exact h.trans_lt response_row_arithmetic.1
  · rw [hA] at h
    exact h.trans_lt response_row_arithmetic.2.1

theorem even_response_rows (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Even) :
    (∑ B : Even, |G A.val B.val|) < (1024/255 : ℝ)*(229/100) := by
  have h := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset Even)) =>
    entry_abs_le_radius G hG ⟨A.val, even_interior A⟩ ⟨B.val, even_interior B⟩)
  rw [even_row_classification responseRadius A.val (Or.inr A.property), A.property] at h
  exact h.trans_lt response_row_arithmetic.2.2

def sizeMetric (w v j : ℕ) : ℝ :=
  ActivityEffectiveMetric.xi^(w+v-2*j) -
    (ActivityEffectiveMetric.xi^(w+v) + ActivityEffectiveMetric.xi^(8-(w+v)) -
      ActivityEffectiveMetric.xi^((8+w)-v) - ActivityEffectiveMetric.xi^((8-w)+v)) /
      (1-ActivityEffectiveMetric.xi^8)
def crossRadius (w v j : ℕ) : ℝ :=
  max (|comparisonLambda*sizeMetric w v j - (sizeInterval w v j).2|)
    (|comparisonLambda*sizeMetric w v j - (sizeInterval w v j).1|)
def crossPairCap : ℝ := crossRadius 1 2 1 + crossRadius 1 2 0

theorem offRadius_eq (A B : Fin 16) :
    offRadius A B = crossRadius (maskSize A) (maskSize B)
      (maskSize (maskIntersection A B)) := by
  simp only [offRadius, crossRadius, gramInterval, sizeInterval, sizeMetric,
    effectiveMetric_formula]

theorem cross_row_arithmetic :
    evenRow crossRadius 1 = 3*crossPairCap ∧
    evenRow crossRadius 3 = 3*crossPairCap ∧
    oddRow crossRadius 2 = 4*crossPairCap ∧
    0 ≤ crossPairCap ∧ crossPairCap < (5/6 : ℝ) := by
  norm_num [evenRow, oddRow, crossPairCap, crossRadius, sizeMetric, sizeInterval,
    scaleInterval, compressedInterval, concreteResources, frameFactor,
    ActivityPairIntervals.xi, ActivityEffectiveMetric.xi, comparisonLambda,
    ByteLineBounds.a3, ByteLineBounds.cubeBound, ByteGramResources.cubeNumerator,
    ByteLineBounds.b3, ByteLineBounds.mixedCubeBound, LineOverlap.eta1,
    LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag, MixedCodeBounds.f3,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3]

def crossKernel (G : Fin 16 → Fin 16 → ℝ) (A : Odd) (B : Even) : ℝ :=
  residualEntry G A.val B.val

theorem cross_rows (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Odd) :
    (∑ B : Even, |crossKernel G A B|) ≤ 3*crossPairCap := by
  have h := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset Even)) =>
    residual_abs_le_offRadius G hG ⟨A.val, odd_interior A⟩ ⟨B.val, even_interior B⟩)
  simp_rw [offRadius_eq] at h
  rw [even_row_classification crossRadius A.val (Or.inl A.property)] at h
  rcases A.property with hA | hA
  · rw [hA, cross_row_arithmetic.1] at h
    exact h
  · rw [hA, cross_row_arithmetic.2.1] at h
    exact h

theorem cross_columns (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) (B : Even) :
    (∑ A : Odd, |crossKernel G A B|) ≤ 4*crossPairCap := by
  have h := Finset.sum_le_sum (fun A (_ : A ∈ (Finset.univ : Finset Odd)) =>
    residual_abs_le_offRadius G hG ⟨B.val, even_interior B⟩ ⟨A.val, odd_interior A⟩)
  simp_rw [offRadius_eq] at h
  rw [odd_row_classification crossRadius B.val (Or.inr B.property), B.property,
    cross_row_arithmetic.2.2.1] at h
  have he (A : Odd) : crossKernel G A B = residualEntry G B.val A.val := by
    unfold crossKernel residualEntry
    rw [DampedDegreeThree.effectiveMetric_symmetric, hsym]
  simp_rw [he]
  exact h

/-- The paper's cross-parity operator bound, for the actual interval-controlled
matrix. The common strict pair cap makes the norm strict uniformly. -/
theorem cross_operator_norm_sq_lt (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (hsym : ∀ A B, G A B = G B A) :
    ‖PaperKernelBounds.kernelOperator (crossKernel G)‖^2 < (25/3 : ℝ) := by
  have hp := cross_row_arithmetic.2.2.2.1
  have hcap := cross_row_arithmetic.2.2.2.2
  have h := PaperKernelBounds.schur_operator_norm_sq (crossKernel G)
    (fun A B => |crossKernel G A B|) (3*crossPairCap) (4*crossPairCap)
    (by positivity) (by positivity) (fun _ _ => abs_nonneg _)
    (fun _ _ => by rw [Real.norm_eq_abs]) (cross_rows G hG) (cross_columns G hG hsym)
  nlinarith

theorem actual_parity_bounds (left right : ByteOrientations.Orientation) (inverse : Bool) :
    (∀ A : Odd, (∑ B : Odd, |ActualDegreeThreeGram.degreeThreeGram left right inverse
      A.val B.val|) < (1024/255 : ℝ)*(9/8)) ∧
    (∀ A : Even, (∑ B : Even, |ActualDegreeThreeGram.degreeThreeGram left right inverse
      A.val B.val|) < (1024/255 : ℝ)*(229/100)) ∧
    ‖PaperKernelBounds.kernelOperator
      (crossKernel (ActualDegreeThreeGram.degreeThreeGram left right inverse))‖^2 <
      (25/3 : ℝ) := by
  have hG := PaperDegreeThreeGramPrinted.actual_entry_bounds left right inverse
  exact ⟨odd_response_rows _ hG, even_response_rows _ hG,
    cross_operator_norm_sq_lt _ hG (ActualDegreeThreeGram.degreeThreeGram_symmetric _ _ _)⟩

end AES8.PaperDegreeThreeParityResponse
