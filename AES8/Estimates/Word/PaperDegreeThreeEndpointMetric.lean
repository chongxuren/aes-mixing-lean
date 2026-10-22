import AES8.Math.PaperDegreeThreeTensorSpectrum
import AES8.Math.PaperSymmetricRowQuadratic
import AESConcrete.DampedDegreeThree

/-! The actual endpoint Schur correction and the two parity metric margins.
The correction is bounded on the two actual principal blocks. The tensor lower
bound then gives the printed 31/32 and 63/64 strict quadratic lower bounds.
This proves the load-bearing inequalities by exact rows of the rank-two
correction; a separate coupling-norm equality is not asserted here. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeEndpointMetric
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric
open PaperDegreeThreeParityCounts PaperDegreeThreeTensorSpectrum
set_option autoImplicit false
set_option maxRecDepth 100000

def correction (A B : Fin 16) : ℝ := activityMetric A B - effectiveMetric A B

def sizeCorrection (w v : ℕ) : ℝ :=
  (xi^(w+v) + xi^(8-(w+v)) - xi^((8+w)-v) - xi^((8-w)+v)) / (1-xi^8)

theorem correction_formula (A B : Fin 16) :
    correction A B = sizeCorrection (maskSize A) (maskSize B) := by
  unfold correction
  rw [effectiveMetric_formula, activityMetric_formula]
  unfold sizeCorrection
  ring

theorem correction_symmetric (A B : Fin 16) : correction A B = correction B A := by
  unfold correction
  rw [activityMetric_symmetric, DampedDegreeThree.effectiveMetric_symmetric]

def oddCorrectionCap : ℝ := 4*xi^2*(1+xi^2)^2/(1-xi^4)
def evenCorrectionCap : ℝ := 12*xi^4/(1-xi^4)

theorem correction_row_arithmetic :
    oddRow (fun w v _ => |sizeCorrection w v|) 1 ≤ oddCorrectionCap ∧
    oddRow (fun w v _ => |sizeCorrection w v|) 3 ≤ oddCorrectionCap ∧
    evenRow (fun w v _ => |sizeCorrection w v|) 2 ≤ evenCorrectionCap := by
  norm_num [oddRow, evenRow, sizeCorrection, oddCorrectionCap, evenCorrectionCap, xi]

theorem odd_correction_rows (A : Odd) :
    (∑ B : Odd, |correction A.val B.val|) ≤ oddCorrectionCap := by
  simp_rw [correction_formula]
  rw [odd_row_classification (fun w v _ => |sizeCorrection w v|) A.val
    (Or.inl A.property)]
  rcases A.property with hA | hA
  · rw [hA]; exact correction_row_arithmetic.1
  · rw [hA]; exact correction_row_arithmetic.2.1

theorem even_correction_rows (A : Even) :
    (∑ B : Even, |correction A.val B.val|) ≤ evenCorrectionCap := by
  simp_rw [correction_formula]
  rw [even_row_classification (fun w v _ => |sizeCorrection w v|) A.val
    (Or.inr A.property), A.property]
  exact correction_row_arithmetic.2.2

theorem supported_quadratic_le (P : Fin 16 → Prop) [DecidablePred P]
    (K : Fin 16 → Fin 16 → ℝ) (hsym : ∀ A B, K A B = K B A)
    (cap : ℝ) (hcap : 0 ≤ cap)
    (hrow : ∀ A : {A // P A}, (∑ B : {B // P B}, |K A.val B.val|) ≤ cap)
    (u : Fin 16 → ℝ) (hu : ∀ A, ¬ P A → u A = 0) :
    qForm u K ≤ cap * ∑ A : Fin 16, (u A)^2 := by
  let R : Fin 16 → Fin 16 → ℝ := fun A B => if P A ∧ P B then K A B else 0
  have hR (A B : Fin 16) : R A B = R B A := by
    dsimp [R]
    rw [hsym A B]
    by_cases hA : P A <;> by_cases hB : P B <;> simp [hA, hB]
  have hrows (A : Fin 16) : (∑ B : Fin 16, |R A B|) ≤ cap := by
    by_cases hA : P A
    · have h := hrow ⟨A, hA⟩
      rw [sum_subtype P (fun B => |K A B|)] at h
      simpa only [R, hA, true_and, apply_ite abs, abs_zero] using h
    · simpa only [R, hA, false_and, if_false, abs_zero, Finset.sum_const_zero] using hcap
  have h := PaperSymmetricRowQuadratic.quadratic_le R hR cap hrows u
  have he : qForm u R = qForm u K := by
    unfold qForm
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    by_cases hA : P A
    · by_cases hB : P B
      · simp [R, hA, hB]
      · rw [hu B hB]; ring
    · rw [hu A hA]; ring
  rwa [he] at h

theorem correction_quadratic_sub (u : Fin 16 → ℝ) :
    qForm u effectiveMetric = qForm u activityMetric - qForm u correction := by
  unfold qForm
  simp only [correction, mul_sub, Finset.sum_sub_distrib]
  ring

theorem odd_metric_lower (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsOdd A → u A = 0) :
    ((1-xi^2)^2 - oddCorrectionCap) * ∑ A : Fin 16, (u A)^2 ≤
      qForm u effectiveMetric := by
  have hp : ∀ A, maskSize A % 2 ≠ 1 → u A = 0 := by
    intro A hA
    apply hu A
    intro ha
    rcases ha with ha | ha <;> simp [ha] at hA
  have ht := supported_quadratic_lower u 1 hp
  have hc := supported_quadratic_le IsOdd correction correction_symmetric
    oddCorrectionCap (by norm_num [oddCorrectionCap, xi]) odd_correction_rows u hu
  rw [correction_quadratic_sub]
  nlinarith

theorem even_metric_lower (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsEven A → u A = 0) :
    ((1-xi^2)^2 - evenCorrectionCap) * ∑ A : Fin 16, (u A)^2 ≤
      qForm u effectiveMetric := by
  have hp : ∀ A, maskSize A % 2 ≠ 0 → u A = 0 := by
    intro A hA
    apply hu A
    intro ha
    simp [IsEven] at ha
    simp [ha] at hA
  have ht := supported_quadratic_lower u 0 hp
  have hc := supported_quadratic_le IsEven correction correction_symmetric
    evenCorrectionCap (by norm_num [evenCorrectionCap, xi]) even_correction_rows u hu
  rw [correction_quadratic_sub]
  nlinarith

theorem energy_pos (u : Fin 16 → ℝ) (hne : u ≠ 0) : 0 < ∑ A : Fin 16, (u A)^2 := by
  obtain ⟨A, hA⟩ := Function.ne_iff.mp hne
  have hp : 0 < (u A)^2 := sq_pos_of_ne_zero hA
  have hs := Finset.single_le_sum
    (fun B (_ : B ∈ (Finset.univ : Finset (Fin 16))) => sq_nonneg (u B))
    (Finset.mem_univ A)
  linarith

/-- Strict Loewner lower bound on the actual odd principal metric block. -/
theorem odd_metric_strict (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsOdd A → u A = 0)
    (hne : u ≠ 0) : (31/32 : ℝ) * ∑ A : Fin 16, (u A)^2 < qForm u effectiveMetric := by
  have h := odd_metric_lower u hu
  have hc : (31/32 : ℝ) < (1-xi^2)^2 - oddCorrectionCap := by
    norm_num [xi, oddCorrectionCap]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  exact hp.trans_le h

/-- Strict Loewner lower bound on the actual size-two principal metric block. -/
theorem even_metric_strict (u : Fin 16 → ℝ) (hu : ∀ A, ¬ IsEven A → u A = 0)
    (hne : u ≠ 0) : (63/64 : ℝ) * ∑ A : Fin 16, (u A)^2 < qForm u effectiveMetric := by
  have h := even_metric_lower u hu
  have hc : (63/64 : ℝ) < (1-xi^2)^2 - evenCorrectionCap := by
    norm_num [xi, evenCorrectionCap]
  have hp := mul_lt_mul_of_pos_right hc (energy_pos u hne)
  exact hp.trans_le h

end AES8.PaperDegreeThreeEndpointMetric
