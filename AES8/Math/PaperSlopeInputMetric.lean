import AES8.Math.PaperSlopeMask
import AESConcrete.WeightedDiagonalDominance

/-! The actual sign-changed effective input metric and its positive distance
inverse. Fixed-denominator integer certificates avoid opaque rational arithmetic.
All properties concern the actual sixteen-column frame after endpoint removal;
there is no diffusion-map or target quadratic-bound premise. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeInputMetric
open PaperSlopeCoincidenceMatrix PaperSlopeMask
set_option autoImplicit false
set_option maxRecDepth 100000

def metricDen : ℤ := 16^4 * (16^8-1)
def inverseDen : ℤ := 255^4

def integerMetric : Matrix Interior Interior ℤ := fun A B =>
  (-1 : ℤ)^(A.val.card+B.val.card) *
    (16^(4-subsetDistance A.val B.val) * (16^8-1) -
      16^(12-A.val.card-B.val.card) - 16^(4+A.val.card+B.val.card) +
      16^(4-A.val.card+B.val.card) + 16^(4+A.val.card-B.val.card))

def integerInverse : Matrix Interior Interior ℤ := fun A B =>
  16^(8-subsetDistance A.val B.val)

theorem integer_symmetric (A B : Interior) : integerMetric A B = integerMetric B A := by
  revert A B
  decide

theorem integer_inverse (A B : Interior) :
    (∑ C : Interior, integerMetric A C * integerInverse C B) =
      if A = B then metricDen * inverseDen else 0 := by
  revert A B
  decide

theorem integer_diagonal (A : Interior) :
    (∑ B : Interior, if A = B then 0 else |integerMetric A B|) ≤ integerMetric A A := by
  revert A
  decide

def metric : Matrix Interior Interior ℝ := fun A B => (integerMetric A B : ℝ) / metricDen
def inverse : Matrix Interior Interior ℝ := fun A B => (integerInverse A B : ℝ) / inverseDen

theorem subsetDistance_le (A B : Finset (Fin 4)) : subsetDistance A B ≤ 4 := by
  revert A B
  decide

theorem metric_formula (A B : Interior) :
    metric A B = (-1 : ℝ)^(A.val.card+B.val.card) *
    ((1/16 : ℝ)^subsetDistance A.val B.val -
      ((1/16 : ℝ)^(A.val.card+B.val.card) +
        (1/16 : ℝ)^(8-A.val.card-B.val.card) -
        (1/16 : ℝ)^(8+A.val.card-B.val.card) -
        (1/16 : ℝ)^(8-A.val.card+B.val.card)) / (1-(1/16 : ℝ)^8)) := by
  have ha1 := A.property.1
  have ha3 := A.property.2
  have hb1 := B.property.1
  have hb3 := B.property.2
  have hd := subsetDistance_le A.val B.val
  unfold metric integerMetric
  generalize A.val.card = a at *
  generalize B.val.card = b at *
  generalize subsetDistance A.val B.val = d at *
  interval_cases a <;> interval_cases b <;> interval_cases d <;> norm_num [metricDen]

theorem inverse_eq (A B : Interior) :
    inverse A B = (256/255 : ℝ)^4 * (1/16 : ℝ)^subsetDistance A.val B.val := by
  have hd := subsetDistance_le A.val B.val
  unfold inverse integerInverse
  generalize subsetDistance A.val B.val = d at *
  interval_cases d <;> norm_num [inverseDen]

theorem metric_symmetric (A B : Interior) : metric A B = metric B A := by
  unfold metric
  rw [integer_symmetric A B]

theorem metric_inverse (A B : Interior) :
    (∑ C : Interior, metric A C * inverse C B) = if A = B then 1 else 0 := by
  have hi := integer_inverse A B
  have hic : (∑ C : Interior, (integerMetric A C : ℝ) * (integerInverse C B : ℝ)) =
      if A = B then (metricDen : ℝ) * inverseDen else 0 := by
    exact_mod_cast hi
  simp only [metric, inverse, div_mul_div_comm, ← Finset.sum_div]
  rw [hic]
  split_ifs <;> norm_num [metricDen, inverseDen]

theorem metric_mul_inverse : metric * inverse = 1 := by
  ext A B
  exact metric_inverse A B

theorem metric_nonneg (x : Interior → ℝ) :
    0 ≤ ∑ A : Interior, ∑ B : Interior, x A * x B * metric A B := by
  apply AESConcrete.WeightedDiagonalDominance.quadratic_nonneg_of_diagonal_dominance
    metric metric_symmetric
  intro A
  have h : (∑ B : Interior, if A = B then (0 : ℝ) else |(integerMetric A B : ℝ)|) ≤
      (integerMetric A A : ℝ) := by exact_mod_cast integer_diagonal A
  change (∑ B : Interior, if A = B then 0 else |metric A B|) ≤ metric A A
  have hd : 0 < (metricDen : ℝ) := by norm_num [metricDen]
  simp only [metric, abs_div, abs_of_pos hd]
  have he : (∑ B : Interior, if A = B then (0 : ℝ) else
      |(integerMetric A B : ℝ)| / (metricDen : ℝ)) =
      (∑ B : Interior, if A = B then (0 : ℝ) else |(integerMetric A B : ℝ)|) /
        (metricDen : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs <;> simp
  rw [he]
  exact div_le_div_of_nonneg_right h hd.le

/-- The positive-semidefinite interface in matrix-vector notation. -/
theorem metric_dot_nonneg (x : Interior → ℝ) : 0 ≤ x ⬝ᵥ (metric *ᵥ x) := by
  have h := metric_nonneg x
  convert h using 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem inverse_symmetric (A B : Interior) : inverse A B = inverse B A := by
  rw [inverse_eq, inverse_eq]
  congr 2
  unfold subsetDistance
  rw [Finset.union_comm]

theorem inverse_nonneg (A B : Interior) : 0 ≤ inverse A B := by
  rw [inverse_eq]
  positivity

theorem actual_effective_metric (A B : Interior) :
    metric A B = (-1 : ℝ)^(A.val.card+B.val.card) *
      AESConcrete.ActivityEffectiveMetric.effectiveMetric
        (PaperSlopeMask.mask A.val) (PaperSlopeMask.mask B.val) := by
  rw [metric_formula, AESConcrete.ActivityEffectiveMetric.effectiveMetric_formula,
    PaperSlopeMask.mask_size, PaperSlopeMask.mask_size, PaperSlopeMask.mask_inter_size]
  simp only [PaperSlopeMask.distance_formula, Nat.sub_sub,
    AESConcrete.ActivityEffectiveMetric.xi]

end AES8.PaperSlopeInputMetric
