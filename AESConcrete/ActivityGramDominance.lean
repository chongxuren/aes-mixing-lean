import AESConcrete.ActivityEffectiveMetric
import AESConcrete.ActivityPairIntervals

/-!
# Exact finite weighted row comparison for the activity Gram intervals

This module proves a finite arithmetic certificate for lambda=(33/10)^2,
the actual effective activity metric, and four times the inverse-frame
compressed intervals.  It then transfers that certificate to an arbitrary
matrix G satisfying those entry intervals.  Positive semidefiniteness and
operator consequences require a separate signed weighted-dominance theorem.
Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityGramDominance
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ActivityEffectiveMetric (Interior effectiveMetric)

set_option maxRecDepth 100000

def comparisonLambda : ℝ := (33/10)^2
def rowWeight (A : Fin 16) : ℝ := if maskSize A = 2 then 5 else 2

def gramInterval (A B : Fin 16) : ℝ × ℝ :=
  ActivityPairIntervals.scaleInterval (4*ActivityPairIntervals.frameFactor)
    (ActivityPairIntervals.compressedInterval ActivityPairIntervals.concreteResources
      (maskSize A) (maskSize B) (maskSize (maskIntersection A B)))

def diagonalLower (A : Fin 16) : ℝ :=
  comparisonLambda*effectiveMetric A A - (gramInterval A A).2

def offRadius (A B : Fin 16) : ℝ :=
  max (|comparisonLambda*effectiveMetric A B - (gramInterval A B).2|)
    (|comparisonLambda*effectiveMetric A B - (gramInterval A B).1|)

def rowOffRadius (A : Fin 16) : ℝ :=
  ∑ B : Fin 16, if B = 0 ∨ B = 15 ∨ B = A then 0 else rowWeight B*offRadius A B

def certificateMargin (A : Fin 16) : ℝ := rowWeight A*diagonalLower A-rowOffRadius A

/-- Numeric four-bit counts let the rational certificate reduce only small
natural expressions. Their equivalence to the actual masks is proved below. -/
private def fourBitCount (n : ℕ) : ℕ :=
  (if n%2 = 1 then 1 else 0) + (if n/2%2 = 1 then 1 else 0) +
    (if n/4%2 = 1 then 1 else 0) + (if n/8%2 = 1 then 1 else 0)

private def commonBitCount (n m : ℕ) : ℕ :=
  (if n%2 = 1 ∧ m%2 = 1 then 1 else 0) +
    (if n/2%2 = 1 ∧ m/2%2 = 1 then 1 else 0) +
    (if n/4%2 = 1 ∧ m/4%2 = 1 then 1 else 0) +
    (if n/8%2 = 1 ∧ m/8%2 = 1 then 1 else 0)

private theorem mask_size_numeric : ∀ A : Fin 16, maskSize A = fourBitCount A.val := by decide

private theorem intersection_size_numeric : ∀ A B : Fin 16,
    maskSize (maskIntersection A B) = commonBitCount A.val B.val := by decide

private theorem intersection_size_self : ∀ A : Fin 16,
    maskSize (maskIntersection A A) = maskSize A := by decide

private theorem interior_size_cases : ∀ A : Fin 16, A ≠ 0 → A ≠ 15 →
    maskSize A = 1 ∨ maskSize A = 2 ∨ maskSize A = 3 := by decide

/-- The actual row sum has only three combinatorial forms. Keep this
classification symbolic, so the large rational resources are not normalized
once for every labelled mask and every column. -/
private def classifiedRow (F : ℕ → ℕ → ℕ → ℝ) (w : ℕ) : ℝ :=
  if w = 1 then
    3*F 1 1 0 + 3*F 1 2 1 + 3*F 1 2 0 + 3*F 1 3 1 + F 1 3 0
  else if w = 2 then
    2*F 2 1 1 + 2*F 2 1 0 + 4*F 2 2 1 + F 2 2 0 +
      2*F 2 3 2 + 2*F 2 3 1
  else if w = 3 then
    3*F 3 1 1 + F 3 1 0 + 3*F 3 2 2 + 3*F 3 2 1 + 3*F 3 3 2
  else 0

private theorem sum_fin_zero (f : Fin 0 → ℝ) : (∑ i, f i) = 0 := by simp

/-- Expand the index set while the summand is still an opaque function.
This keeps recursive successor lambdas out of the mask simplification. -/
private theorem sum_fin_sixteen (f : Fin 16 → ℝ) :
    (∑ B : Fin 16, f B) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
        (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + 0))))))))))))))) := by
  simp only [Fin.sum_univ_succ, sum_fin_zero]
  rfl

private theorem symbolic_row_classification (F : ℕ → ℕ → ℕ → ℝ)
    (A : Fin 16) (h0 : A ≠ 0) (h15 : A ≠ 15) :
    (∑ B : Fin 16, if B = 0 ∨ B = 15 ∨ B = A then 0 else
      F (maskSize A) (maskSize B) (maskSize (maskIntersection A B))) =
      classifiedRow F (maskSize A) := by
  rw [sum_fin_sixteen]
  -- Intersections must reduce before the general size lemma hides the mask.
  simp_rw [intersection_size_numeric, mask_size_numeric]
  fin_cases A <;>
    norm_num [classifiedRow, fourBitCount, commonBitCount, Fin.ext_iff] at * <;> ring

private def sizeWeight (w : ℕ) : ℝ := if w = 2 then 5 else 2

private def sizeMetric (w v j : ℕ) : ℝ :=
  ActivityEffectiveMetric.xi^(w+v-2*j) -
    (ActivityEffectiveMetric.xi^(w+v) + ActivityEffectiveMetric.xi^(8-(w+v)) -
      ActivityEffectiveMetric.xi^((8+w)-v) - ActivityEffectiveMetric.xi^((8-w)+v)) /
      (1-ActivityEffectiveMetric.xi^8)

private def sizeInterval (w v j : ℕ) : ℝ × ℝ :=
  ActivityPairIntervals.scaleInterval (4*ActivityPairIntervals.frameFactor)
    (ActivityPairIntervals.compressedInterval ActivityPairIntervals.concreteResources w v j)

private def sizeDiagonal (w : ℕ) : ℝ :=
  comparisonLambda*sizeMetric w w w - (sizeInterval w w w).2

private def sizeRadius (w v j : ℕ) : ℝ :=
  max (|comparisonLambda*sizeMetric w v j - (sizeInterval w v j).2|)
    (|comparisonLambda*sizeMetric w v j - (sizeInterval w v j).1|)

private def sizeMargin (w : ℕ) : ℝ :=
  sizeWeight w*sizeDiagonal w -
    classifiedRow (fun w v j => sizeWeight v*sizeRadius w v j) w

private theorem offRadius_eq (A B : Fin 16) :
    offRadius A B = sizeRadius (maskSize A) (maskSize B)
      (maskSize (maskIntersection A B)) := by
  simp only [offRadius, sizeRadius, gramInterval, sizeInterval, sizeMetric,
    ActivityEffectiveMetric.effectiveMetric_formula]

private theorem diagonalLower_eq (A : Fin 16) :
    diagonalLower A = sizeDiagonal (maskSize A) := by
  simp only [diagonalLower, sizeDiagonal, gramInterval, sizeInterval, sizeMetric,
    ActivityEffectiveMetric.effectiveMetric_formula, intersection_size_self]

private theorem rowOffRadius_eq (A : Fin 16) (h0 : A ≠ 0) (h15 : A ≠ 15) :
    rowOffRadius A =
      classifiedRow (fun w v j => sizeWeight v*sizeRadius w v j) (maskSize A) := by
  unfold rowOffRadius rowWeight
  simp_rw [offRadius_eq]
  exact symbolic_row_classification
    (fun w v j => sizeWeight v*sizeRadius w v j) A h0 h15

private theorem certificateMargin_eq (A : Fin 16) (h0 : A ≠ 0) (h15 : A ≠ 15) :
    certificateMargin A = sizeMargin (maskSize A) := by
  simp only [certificateMargin, sizeMargin, rowWeight, sizeWeight,
    diagonalLower_eq, rowOffRadius_eq A h0 h15]

/-- Only these three size rows perform the large exact rational arithmetic.
No numerical margin or floating-point result is supplied as a premise. -/
private theorem sizeMargin_pos (w : ℕ) (hw : w = 1 ∨ w = 2 ∨ w = 3) :
    0 < sizeMargin w := by
  rcases hw with rfl | rfl | rfl <;>
    norm_num [sizeMargin, sizeWeight, sizeDiagonal, sizeRadius, classifiedRow,
      sizeMetric, sizeInterval, comparisonLambda, ActivityPairIntervals.scaleInterval,
      ActivityPairIntervals.compressedInterval, ActivityPairIntervals.concreteResources,
      ActivityPairIntervals.frameFactor, ActivityPairIntervals.xi, ActivityEffectiveMetric.xi,
      ByteLineBounds.a3, ByteLineBounds.cubeBound, ByteGramResources.cubeNumerator,
      ByteLineBounds.b3, ByteLineBounds.mixedCubeBound, LineOverlap.eta1, LineOverlap.eta2,
      LineOverlap.delta, LineOverlap.offdiag, MixedCodeBounds.f3,
      ContainmentCodeBounds.z3, ContainmentCodeBounds.h3]

/-- Exact finite arithmetic for every actual interior mask, assembled from
the symbolic row classification and the three proved rational inequalities. -/
theorem exact_certificate : ∀ A : Fin 16, A ≠ 0 → A ≠ 15 → 0 < certificateMargin A := by
  intro A h0 h15
  rw [certificateMargin_eq A h0 h15]
  exact sizeMargin_pos (maskSize A) (interior_size_cases A h0 h15)

theorem rowWeight_pos (A : Fin 16) : 0 < rowWeight A := by
  unfold rowWeight
  split_ifs <;> norm_num

def residualEntry (G : Fin 16 → Fin 16 → ℝ) (A B : Fin 16) : ℝ :=
  comparisonLambda*effectiveMetric A B-G A B

def EntryBounds (G : Fin 16 → Fin 16 → ℝ) : Prop :=
  ∀ A B : Interior, ActivityPairIntervals.inInterval (gramInterval A.val B.val) (G A.val B.val)

def actualOffSum (G : Fin 16 → Fin 16 → ℝ) (A : Fin 16) : ℝ :=
  ∑ B : Fin 16, if B = 0 ∨ B = 15 ∨ B = A then 0 else rowWeight B*|residualEntry G A B|

/-- Endpoint membership gives the required diagonal lower bound. -/
theorem diagonalLower_le (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Interior) :
    diagonalLower A.val ≤ residualEntry G A.val A.val := by
  have h := (hG A A).2
  unfold diagonalLower residualEntry
  linarith

/-- The largest endpoint absolute value bounds every interior entry. -/
theorem residual_abs_le_offRadius (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (A B : Interior) : |residualEntry G A.val B.val| ≤ offRadius A.val B.val := by
  rcases hG A B with ⟨hl, hu⟩
  unfold residualEntry offRadius
  apply abs_le.mpr
  have hleft := neg_abs_le (comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).2)
  have hright := le_abs_self (comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).1)
  have hmleft := le_max_left
    (|comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).2|)
    (|comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).1|)
  have hmright := le_max_right
    (|comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).2|)
    (|comparisonLambda*effectiveMetric A.val B.val-(gramInterval A.val B.val).1|)
  constructor <;> linarith

theorem actualOffSum_le (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G) (A : Interior) :
    actualOffSum G A.val ≤ rowOffRadius A.val := by
  unfold actualOffSum rowOffRadius
  apply Finset.sum_le_sum
  intro B _
  by_cases hb : B = 0 ∨ B = 15 ∨ B = A.val
  · simp [hb]
  · simp only [if_neg hb]
    have hB0 : B ≠ 0 := fun h => hb (Or.inl h)
    have hB15 : B ≠ 15 := fun h => hb (Or.inr (Or.inl h))
    exact mul_le_mul_of_nonneg_left
      (residual_abs_le_offRadius G hG A ⟨B, hB0, hB15⟩) (le_of_lt (rowWeight_pos B))

/-- Transfer of the independently proved finite numerical certificate. -/
theorem weighted_row_dominance_full (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (A : Interior) :
    0 < rowWeight A.val*residualEntry G A.val A.val-actualOffSum G A.val := by
  have hc := exact_certificate A.val A.property.1 A.property.2
  have hd := mul_le_mul_of_nonneg_left (diagonalLower_le G hG A) (le_of_lt (rowWeight_pos A.val))
  have hs := actualOffSum_le G hG A
  unfold certificateMargin at hc
  linarith

private theorem interior_sum (f : Fin 16 → ℝ) :
    (∑ B : Interior, f B.val) = ∑ B : Fin 16, if B ≠ 0 ∧ B ≠ 15 then f B else 0 := by
  classical
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem actualOffSum_eq_interior (G : Fin 16 → Fin 16 → ℝ) (A : Interior) :
    actualOffSum G A.val = ∑ B : Interior,
      if B.val = A.val then 0 else rowWeight B.val*|residualEntry G A.val B.val| := by
  rw [interior_sum (fun B : Fin 16 => if B = A.val then 0 else
    rowWeight B*|residualEntry G A.val B|)]
  unfold actualOffSum
  apply Finset.sum_congr rfl
  intro B _
  by_cases h0 : B = 0 <;> by_cases h15 : B = 15 <;> by_cases hA : B = A.val <;>
    simp [h0, h15, hA]

/-- The promised generic matrix API on the fourteen interior masks. This
is a weighted row inequality only; no PSD/operator theorem is claimed here. -/
theorem weighted_row_dominance (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (A : Interior) :
    0 < rowWeight A.val*(comparisonLambda*effectiveMetric A.val A.val-G A.val A.val) -
      ∑ B : Interior, if B.val = A.val then 0 else
        rowWeight B.val*|comparisonLambda*effectiveMetric A.val B.val-G A.val B.val| := by
  have h := weighted_row_dominance_full G hG A
  rw [actualOffSum_eq_interior] at h
  exact h

end AESConcrete.ActivityGramDominance
