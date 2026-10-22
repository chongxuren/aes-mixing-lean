import AES8.Math.LiteralMetricSquareRoot
import AES8.Math.PaperSlopeMetricComparison

/-!
The paper's literal slope route, instantiated at the fourteen retained input
subsets. The existing finite certificates supply only the actual metric,
its inverse, class counts, positive weights, and strict weighted rows. The
spectral comparison below is obtained from the constructed metric roots,
similarity, and the maximum-row-sum spectral argument. It does not invoke
`PaperSlopeMetricComparison.exists_coefficient_margin` or any Schur substitute.

Candidate source; formal-node compilation belongs to the root task. No local
Lean/tests, manuscript edits, canonical edits, or attacks are in scope.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal NNReal

namespace AES8.PaperSlopeLiteral

open PaperSlopeCoincidenceMatrix PaperSlopeCoincidences PaperSymbolicSlopeTable
open PaperSlopeInputMetric PaperSlopeOutputFrame

set_option autoImplicit false

/-- Equality classes partition a positive output-distance Gram form into a
sum of positive forms. This supplies the PSD property of the actual `J`. -/
theorem slope_class_distance_nonneg (p : Fin 6) (u : Interior → ℝ) :
    0 ≤ ∑ k : Fin 20, ∑ l : Fin 20,
      if slopeClass (pairType p) k = slopeClass (pairType p) l then
        u (inputIndex p k) * u (inputIndex p l) *
          (1/16 : ℝ)^outputDistance p k l else 0 := by
  have hs : 0 ≤ ∑ c : Fin 20, ∑ k : Fin 20, ∑ l : Fin 20,
      (if slopeClass (pairType p) k = c then u (inputIndex p k) else 0) *
      (if slopeClass (pairType p) l = c then u (inputIndex p l) else 0) *
      (1/16 : ℝ)^outputDistance p k l :=
    Finset.sum_nonneg (fun c _ => distance_quadratic_nonneg p
      (fun k => if slopeClass (pairType p) k = c then u (inputIndex p k) else 0))
  have he :
      (∑ c : Fin 20, ∑ k : Fin 20, ∑ l : Fin 20,
        (if slopeClass (pairType p) k = c then u (inputIndex p k) else 0) *
        (if slopeClass (pairType p) l = c then u (inputIndex p l) else 0) *
        (1/16 : ℝ)^outputDistance p k l) =
      ∑ k : Fin 20, ∑ l : Fin 20,
        if slopeClass (pairType p) k = slopeClass (pairType p) l then
          u (inputIndex p k) * u (inputIndex p l) *
            (1/16 : ℝ)^outputDistance p k l else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    simp only [ite_mul, zero_mul, mul_ite, mul_zero]
    simp [eq_comm]
  rwa [he] at hs

theorem coincidence_posSemidef : (matrix (1/16)).PosSemidef := by
  have hsym : (matrix (1/16)).IsHermitian := by
    ext A B
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      (matrix_symmetric (1/16) A B).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro x
  have hn : 0 ≤ ∑ A : Interior, ∑ B : Interior,
      x A * x B * matrix (1/16) A B := by
    rw [PaperSlopeClassGram.matrix_quadratic]
    exact Finset.sum_nonneg (fun p _ => slope_class_distance_nonneg p x)
  simpa only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using hn

theorem actual_metric_posSemidef : metric.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext A B
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      (metric_symmetric A B).symm
  · intro x
    simpa only [star_trivial] using metric_dot_nonneg x

theorem inverse_mul_metric : inverse * metric = 1 := by
  have hK : metricᵀ = metric := by
    ext A B
    exact metric_symmetric B A
  have hH : inverseᵀ = inverse := by
    ext A B
    exact inverse_symmetric B A
  have h := congrArg Matrix.transpose metric_mul_inverse
  simpa only [Matrix.transpose_mul, Matrix.transpose_one, hK, hH] using h

def actualS : Matrix Interior Interior ℝ := inverseSqrtMetric actual_metric_posSemidef
def actualR : Matrix Interior Interior ℝ := sqrtMetric actual_metric_posSemidef
def actualQ : Matrix Interior Interior ℝ := gramComparison actualS (matrix (1/16)) (256/255)
def actualP : Matrix Interior Interior ℝ := comparisonProduct inverse (matrix (1/16)) (256/255)
def actualW : Matrix Interior Interior ℝ := weightDiagonal PaperSlopeMetricComparison.coordinateWeight
def actualWi : Matrix Interior Interior ℝ := inverseWeightDiagonal PaperSlopeMetricComparison.coordinateWeight
def actualT : Matrix Interior Interior ℝ :=
  weightedSimilar actualP PaperSlopeMetricComparison.coordinateWeight

theorem actualS_mul_actualR : actualS * actualR = 1 :=
  inverseSqrtMetric_mul_sqrtMetric metric inverse actual_metric_posSemidef inverse_mul_metric

theorem actualR_mul_actualS : actualR * actualS = 1 :=
  sqrtMetric_mul_inverseSqrtMetric metric inverse actual_metric_posSemidef inverse_mul_metric

theorem actualR_sq : actualR * actualR = metric :=
  sqrtMetric_sq metric inverse actual_metric_posSemidef inverse_mul_metric

theorem actualS_sq : actualS * actualS = inverse :=
  inverseSqrtMetric_sq metric inverse actual_metric_posSemidef metric_mul_inverse inverse_mul_metric

theorem actualQ_posSemidef : actualQ.PosSemidef :=
  gramComparison_posSemidef actualS (matrix (1/16))
    (inverseSqrtMetric_posSemidef actual_metric_posSemidef).isHermitian
    coincidence_posSemidef (256/255) (by norm_num)

/-- The comparison product is literally the printed `C₀⁵ D J`. -/
theorem actualP_eq_printed :
    actualP = (256/255 : ℝ)^5 • (PaperSlopeDistanceMatrix.distanceKernel * matrix (1/16)) := by
  unfold actualP comparisonProduct
  rw [PaperSlopeMetricComparison.inverse_eq_distance, Matrix.smul_mul, smul_smul]
  congr 1
  ring

theorem actual_similarity : actualS * actualQ * actualR = actualP :=
  gramComparison_similar_product metric inverse (matrix (1/16)) actual_metric_posSemidef
    metric_mul_inverse inverse_mul_metric (256/255)

theorem actualP_spectrum_eq_actualQ : spectrum ℝ actualP = spectrum ℝ actualQ := by
  rw [← actual_similarity]
  exact similarity_spectrum actualS actualR actualS_mul_actualR actualR_mul_actualS actualQ

theorem actualP_radius_eq_actualQ : spectralRadius ℝ actualP = spectralRadius ℝ actualQ := by
  unfold spectralRadius
  rw [actualP_spectrum_eq_actualQ]

theorem actualP_nonneg (A B : Interior) : 0 ≤ actualP A B := by
  change 0 ≤ (256/255 : ℝ) * ∑ C : Interior, inverse A C * matrix (1/16) C B
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun C _ =>
    mul_nonneg (inverse_nonneg A C) (matrix_nonneg (1/16) (by norm_num) C B))

theorem actualW_mul_actualWi : actualW * actualWi = 1 :=
  weight_inverse _ PaperSlopeMetricComparison.coordinateWeight_pos

theorem actualWi_mul_actualW : actualWi * actualW = 1 :=
  inverse_weight _ PaperSlopeMetricComparison.coordinateWeight_pos

theorem actualT_apply (A B : Interior) :
    actualT A B = actualP A B * PaperSlopeMetricComparison.coordinateWeight B /
      PaperSlopeMetricComparison.coordinateWeight A :=
  weightedSimilar_apply actualP PaperSlopeMetricComparison.coordinateWeight A B

theorem actualT_nonneg (A B : Interior) : 0 ≤ actualT A B :=
  weightedSimilar_nonneg actualP actualP_nonneg _ PaperSlopeMetricComparison.coordinateWeight_pos A B

theorem actualT_rows (A : Interior) : (∑ B, actualT A B) < (66/5 : ℝ) := by
  rw [actualT, weightedSimilar_rows]
  apply (div_lt_iff₀ (PaperSlopeMetricComparison.coordinateWeight_pos A)).mpr
  simpa only [actualP, comparisonProduct, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul] using PaperSlopeMetricComparison.product_weighted_rows A

theorem actualT_spectrum_eq_actualP : spectrum ℝ actualT = spectrum ℝ actualP :=
  weightedSimilar_spectrum actualP _ PaperSlopeMetricComparison.coordinateWeight_pos

theorem actualT_radius_eq_actualP : spectralRadius ℝ actualT = spectralRadius ℝ actualP :=
  weightedSimilar_spectralRadius actualP _ PaperSlopeMetricComparison.coordinateWeight_pos

/-- The finite maximum row sum bounds the whole spectrum with a single
strict margin below `66/5`. -/
theorem actual_spectral_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧
      ∀ i, |actualQ_posSemidef.isHermitian.eigenvalues i| ≤ a := by
  obtain ⟨a, ha, har, hspectrum⟩ :=
    exists_row_spectral_margin actualT actualT_nonneg (66/5) (by norm_num) actualT_rows
  refine ⟨a, ha, har, fun i => hspectrum _ ?_⟩
  rw [actualT_spectrum_eq_actualP, actualP_spectrum_eq_actualQ]
  exact actualQ_posSemidef.isHermitian.eigenvalues_mem_spectrum_real i

theorem actual_spectralRadius_lt :
    spectralRadius ℝ actualP < ((66/5 : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨a, ha, har, hspectrum⟩ :=
    exists_row_spectral_margin actualT actualT_nonneg (66/5) (by norm_num) actualT_rows
  let aNN : ℝ≥0 := ⟨a, ha.le⟩
  have hradius : spectralRadius ℝ actualT ≤ (aNN : ℝ≥0∞) := by
    unfold spectralRadius
    refine iSup₂_le fun μ hμ => ?_
    apply ENNReal.coe_le_coe.mpr
    change ‖μ‖ ≤ a
    have h := hspectrum μ hμ
    simpa only [Real.norm_eq_abs] using h
  rw [← actualT_radius_eq_actualP]
  apply hradius.trans_lt
  apply ENNReal.coe_lt_coe.mpr
  exact_mod_cast har

/-- The symmetric PSD comparison has Euclidean operator norm below `66/5`,
proved from its spectrum and the positive diagonal row comparison. -/
theorem actualQ_norm_lt : ‖PaperKernelBounds.kernelOperator actualQ‖ < (66/5 : ℝ) := by
  obtain ⟨a, ha, har, heig⟩ := actual_spectral_margin
  exact (PaperFiniteSymmetricNorm.norm_le_eigenvalue_bound actualQ
    actualQ_posSemidef.isHermitian a ha.le heig).trans_lt har

/-- The old endpoint interface is recovered by the literal spectral route.
Every metric, inverse, root, class matrix, and row certificate is actual. -/
theorem exists_coefficient_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ x : Interior → ℝ,
      (256/255 : ℝ) * PaperSlopeMetric.quad (matrix (1/16)) x ≤
        a * PaperSlopeMetric.quad metric x := by
  obtain ⟨a, ha, har, heig⟩ := actual_spectral_margin
  exact ⟨a, ha, har, metric_quadratic_le_of_gram_spectrum metric inverse (matrix (1/16))
    actual_metric_posSemidef inverse_mul_metric (256/255) a
    actualQ_posSemidef.isHermitian heig⟩

theorem exists_classGram_coefficient_margin :
    ∃ a : ℝ, 0 < a ∧ a < 66/5 ∧ ∀ x : Interior → ℝ,
      PaperSlopeClassGram.scaledGram x ≤ a * PaperSlopeMetric.quad metric x := by
  obtain ⟨a, ha, har, hquad⟩ := exists_coefficient_margin
  exact ⟨a, ha, har, fun x =>
    (PaperSlopeMetricComparison.classGram_le_comparison x).trans (hquad x)⟩

/-- This can replace the prior criterion's numeric operator bridge without
changing its physical input/output hypotheses. The root task owns integration. -/
theorem operator_norm_sq_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F) (coeff : E → Interior → ℝ)
    (hinput : ∀ x, PaperSlopeMetric.quad metric (coeff x) ≤ ‖x‖^2)
    (houtput : ∀ x, (256 : ℝ)^2 * ‖B x‖^2 ≤
      (256/255 : ℝ) * PaperSlopeMetric.quad (matrix (1/16)) (coeff x)) :
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
    (hinput : ∀ x, PaperSlopeMetric.quad metric (coeff x) ≤ ‖x‖^2)
    (houtput : ∀ x, (256 : ℝ)^2 * ‖B x‖^2 ≤
      (256/255 : ℝ) * PaperSlopeMetric.quad (matrix (1/16)) (coeff x)) :
    ‖B‖ < (71/5000 : ℝ) := by
  have h := (operator_norm_sq_lt B coeff hinput houtput).trans
    PaperSlopeGroupBounds.squared_norm_comparison
  exact (sq_lt_sq₀ (norm_nonneg B) (by norm_num : (0 : ℝ) ≤ 71/5000)).mp h

end AES8.PaperSlopeLiteral
