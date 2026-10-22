import AES8.Math.PaperSlopeInputMetric
import AES8.Math.PaperSlopeDistanceMatrix
import AES8.Math.PaperSlopeMetric
import AES8.Math.PaperSlopeClassGram

/-!
# Actual input-metric comparison for the slope criterion

The matrices, positive weights, inverse identity and row bounds are all
instantiated. The output residual-Gram correspondence remains a separate
geometric obligation, explicitly required by the operator consequence.
-/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeMetricComparison
open PaperSlopeCoincidenceMatrix PaperSlopeCoincidences PaperSlopeGroupBounds
open PaperSlopeDistanceMatrix PaperSlopeInputMetric PaperSlopeMetric
set_option autoImplicit false

def coordinateWeight (A : Interior) : ℝ := weights (group A.val)

theorem coordinateWeight_pos (A : Interior) : 0 < coordinateWeight A := by
  unfold coordinateWeight
  generalize group A.val = g
  fin_cases g <;> norm_num [weights]

theorem inverse_eq_distance : inverse = (256/255 : ℝ)^4 • distanceKernel := by
  ext A B
  rw [inverse_eq]
  rfl

theorem product_weighted_rows (A : Interior) :
    (256/255 : ℝ) * ((inverse * matrix (1/16)) *ᵥ coordinateWeight) A <
      (66/5 : ℝ) * coordinateWeight A := by
  rw [inverse_eq_distance, Matrix.smul_mul, Matrix.smul_mulVec]
  have h := weighted_rows A
  change (256/255 : ℝ) * ((256/255 : ℝ)^4 *
    ((distanceKernel * matrix (1/16)) *ᵥ coordinateWeight) A) < _
  convert h using 1 <;>
    simp only [PaperGroupedMatrix.action, Matrix.mulVec, dotProduct, coordinateWeight]
  ring

/-- A single actual scalar smaller than 66/5 controls every retained
coefficient vector. No matrix, metric or weighted-row premise remains. -/
theorem exists_coefficient_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ x : Interior → ℝ,
      (256/255 : ℝ) * quad (matrix (1/16)) x ≤ a * quad metric x := by
  exact exists_scaled_quadratic_margin metric inverse (matrix (1/16))
    metric_symmetric metric_dot_nonneg metric_mul_inverse inverse_symmetric inverse_nonneg
    (matrix_symmetric (1/16)) (matrix_nonneg (1/16) (by norm_num))
    coordinateWeight coordinateWeight_pos (256/255) (66/5) (by norm_num) (by norm_num)
    product_weighted_rows

/-- Coefficients after the paper's diagonal parity change. -/
def signedCoefficients (u : Fin 16 → ℝ) (A : Interior) : ℝ :=
  (-1 : ℝ)^A.val.card * u (PaperSlopeMask.mask A.val)

private theorem sign_sq (n : ℕ) : ((-1 : ℝ)^n)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num

theorem metric_eq_effectiveEnergy (u : Fin 16 → ℝ) :
    quad metric (signedCoefficients u) = AESConcrete.ActivityEffectiveMetric.effectiveEnergy u := by
  calc
    _ = ∑ A : Interior, ∑ B : Interior,
        u (PaperSlopeMask.mask A.val) * u (PaperSlopeMask.mask B.val) *
          AESConcrete.ActivityEffectiveMetric.effectiveMetric
            (PaperSlopeMask.mask A.val) (PaperSlopeMask.mask B.val) := by
      simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [actual_effective_metric, pow_add]
      simp only [signedCoefficients]
      calc
        _ = ((-1 : ℝ)^A.val.card)^2 * ((-1 : ℝ)^B.val.card)^2 *
          (u (PaperSlopeMask.mask A.val) * u (PaperSlopeMask.mask B.val) *
            AESConcrete.ActivityEffectiveMetric.effectiveMetric
              (PaperSlopeMask.mask A.val) (PaperSlopeMask.mask B.val)) := by ring
        _ = _ := by rw [sign_sq, sign_sq]; ring
    _ = _ := by
      unfold AESConcrete.ActivityEffectiveMetric.effectiveEnergy AESConcrete.ActivityEffectiveMetric.qForm
      apply Fintype.sum_equiv PaperSlopeMask.interiorEquiv
      intro A
      apply Fintype.sum_equiv PaperSlopeMask.interiorEquiv
      intro B
      rfl

/-- The actual frame synthesis energy controls the effective metric for
all sixteen real coefficients, including arbitrary endpoint coefficients. -/
theorem coefficient_metric_le_frame_energy (u : Fin 16 → ℝ) :
    quad metric (signedCoefficients u) ≤
      ∑ x : Fin 4 → AESMixing.BinaryWord 8,
        (∑ A : Fin 16, AESConcrete.ActivityFrame.frameColumn (AESMixing.AES.maskBit A) x * u A)^2 := by
  rw [metric_eq_effectiveEnergy]
  exact AESConcrete.ActivityEffectiveMetric.actual_frame_energy_ge_effective u

theorem exists_frame_energy_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ u : Fin 16 → ℝ,
      (256/255 : ℝ) * quad (matrix (1/16)) (signedCoefficients u) ≤
        a * ∑ x : Fin 4 → AESMixing.BinaryWord 8,
          (∑ A : Fin 16, AESConcrete.ActivityFrame.frameColumn (AESMixing.AES.maskBit A) x * u A)^2 := by
  obtain ⟨a, ha, har, hquad⟩ := exists_coefficient_margin
  exact ⟨a, ha, har, fun u => (hquad (signedCoefficients u)).trans
    (mul_le_mul_of_nonneg_left (coefficient_metric_le_frame_energy u) ha.le)⟩

theorem classGram_le_comparison (x : Interior → ℝ) :
    PaperSlopeClassGram.scaledGram x ≤ (256/255 : ℝ) * quad (matrix (1/16)) x := by
  convert PaperSlopeClassGram.scaledGram_le x using 1
  simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum]
  congr 1
  funext A
  apply Finset.sum_congr rfl
  intro B _
  ring

/-- The actual normalized class-Gram formula has the same uniform margin.
Identifying this formula with the physical graph contraction remains separate. -/
theorem exists_classGram_coefficient_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ x : Interior → ℝ,
      PaperSlopeClassGram.scaledGram x ≤ a * quad metric x := by
  obtain ⟨a, ha, har, hquad⟩ := exists_coefficient_margin
  exact ⟨a, ha, har, fun x => (classGram_le_comparison x).trans (hquad x)⟩

theorem exists_classGram_frame_energy_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ u : Fin 16 → ℝ,
      PaperSlopeClassGram.scaledGram (signedCoefficients u) ≤
        a * ∑ x : Fin 4 → AESMixing.BinaryWord 8,
          (∑ A : Fin 16, AESConcrete.ActivityFrame.frameColumn (AESMixing.AES.maskBit A) x * u A)^2 := by
  obtain ⟨a, ha, har, hframe⟩ := exists_frame_energy_margin
  exact ⟨a, ha, har, fun u => (classGram_le_comparison (signedCoefficients u)).trans (hframe u)⟩

/-- Conditional operator bridge. The two physical energy statements are
explicit interfaces: this theorem does not establish the residual Gram bound. -/
theorem operator_norm_sq_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F) (coeff : E → Interior → ℝ)
    (hinput : ∀ x, quad metric (coeff x) ≤ ‖x‖^2)
    (houtput : ∀ x, (256 : ℝ)^2 * ‖B x‖^2 ≤
      (256/255 : ℝ) * quad (matrix (1/16)) (coeff x)) :
    ‖B‖^2 < (66/(5*256^2) : ℝ) := by
  obtain ⟨a, ha, har, hquad⟩ := exists_coefficient_margin
  have henergy (x : E) : ‖B x‖^2 ≤ (a/256^2)*‖x‖^2 := by
    have h := (houtput x).trans ((hquad (coeff x)).trans
      (mul_le_mul_of_nonneg_left (hinput x) ha.le))
    nlinarith
  have hn : ‖B‖ ≤ Real.sqrt (a/256^2) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ a/256^2)] using henergy x
  have hs := (sq_le_sq₀ (norm_nonneg B) (Real.sqrt_nonneg (a/256^2))).mpr hn
  rw [Real.sq_sqrt (by positivity : 0 ≤ a/256^2)] at hs
  have hr : a/256^2 < (66/(5*256^2) : ℝ) := by nlinarith
  exact hs.trans_lt hr

theorem operator_norm_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F) (coeff : E → Interior → ℝ)
    (hinput : ∀ x, quad metric (coeff x) ≤ ‖x‖^2)
    (houtput : ∀ x, (256 : ℝ)^2 * ‖B x‖^2 ≤
      (256/255 : ℝ) * quad (matrix (1/16)) (coeff x)) :
    ‖B‖ < (71/5000 : ℝ) := by
  have h := (operator_norm_sq_lt B coeff hinput houtput).trans squared_norm_comparison
  exact (sq_lt_sq₀ (norm_nonneg B) (by norm_num : (0 : ℝ) ≤ 71/5000)).mp h

end AES8.PaperSlopeMetricComparison
