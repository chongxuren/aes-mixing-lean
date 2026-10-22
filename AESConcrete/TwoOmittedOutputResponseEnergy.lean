import AESConcrete.TwoOmittedOutputSplit
import AESConcrete.TwoOmittedOutputScalar
import AESConcrete.OmittedUniformTwoInputResponseEnergy

/-!
# (10,6) same-source response energy

The separate weighted-residual-line theorem supplies only the double-output-
zero term.

The exact R=(W-W_a-W_b+W_ab)/(q-1) identity precedes the L2 triangle. Their
norm numerators are respectively (2s+1)a, (s+2)a, (s+2)a and a over the common
input denominator q-1. The original signed h including h(0) is shared. No
desired estimate, cancellation, injectivity or source-zero premise is assumed.
Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOutputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry (Retained Residual)
open AESConcrete.TwoOmittedOutputRawInputResponse (inputWeightedResponse)
open AESConcrete.TwoOmittedOutputSource
open AESConcrete.TwoOmittedOutputSplit (omittedResponse actualResponse)
open AESConcrete.TwoOmittedOutputScalar
open AESConcrete.ActivityCodeScalar (q s q_sub_one_pos)
open AESConcrete.UniformGraphScalar (rho kappa)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (rawNormNumerator / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  simpa only [rawNormNumerator, normBase, mul_assoc] using
    TwoOmittedOutputRawInputResponse.inputWeightedResponse_energy pOut pIn h

/-- This uses the plan-selected pending input-weighted (9,6) theorem, not its
actual response theorem, which would include an extra omitted-output weight. -/
theorem oneZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, oneZeroResponse pOut pIn a h y ^ 2) ≤
      (oneZeroNormNumerator / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  simpa only [oneZeroResponse, oneZeroNormNumerator, normBase,
    OmittedUniformTwoInputScalar.normBase] using
      OmittedUniformTwoInputResponseEnergy.inputWeightedResponse_energy (oneZero pOut a) pIn h

theorem twoZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, twoZeroResponse pOut pIn h y ^ 2) ≤
      (normBase / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  rw [twoZeroResponse_eq_jointResponse]
  have he := WeightedResidualLineCaps.joint_response_energy
    (twoZero pOut) pIn (by decide : 1 ≤ (1 : Fin 5).val) h
  have hc : WeightedResidualLineCaps.pieceSquaredBound (1 : Fin 5) =
      (normBase / (q - 1)) ^ 2 := by
    change rho ^ 2 * kappa / (q - 1) ^ 2 = (normBase / (q - 1)) ^ 2
    rw [div_pow, normBase_sq]
  rw [hc] at he
  exact he

theorem omittedResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, omittedResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  have ha := div_nonneg rawNormNumerator_nonneg q_sub_one_pos.le
  have hb := div_nonneg oneZeroNormNumerator_nonneg q_sub_one_pos.le
  have he := div_nonneg normBase_nonneg q_sub_one_pos.le
  have hl := TripleResponse.four_response_l2_le
    (inputWeightedResponse pOut pIn h)
    (oneZeroResponse pOut pIn (omittedFirst pOut) h)
    (oneZeroResponse pOut pIn (omittedSecond pOut) h)
    (twoZeroResponse pOut pIn h) h
    (rawNormNumerator / (q - 1)) (oneZeroNormNumerator / (q - 1))
    (oneZeroNormNumerator / (q - 1)) (normBase / (q - 1)) (q - 1)
    ha hb hb he (inputWeightedResponse_energy pOut pIn h)
    (oneZeroResponse_energy pOut pIn (omittedFirst pOut) h)
    (oneZeroResponse_energy pOut pIn (omittedSecond pOut) h)
    (twoZeroResponse_energy pOut pIn h)
  rw [abs_of_nonneg q_sub_one_pos.le] at hl
  rw [← TwoOmittedOutputSplit.omittedResponse_eq_split] at hl
  have hc : 0 ≤ (rawNormNumerator / (q - 1) + oneZeroNormNumerator / (q - 1) +
      oneZeroNormNumerator / (q - 1) + normBase / (q - 1)) / (q - 1) :=
    div_nonneg (add_nonneg (add_nonneg (add_nonneg ha hb) hb) he) q_sub_one_pos.le
  have hs := (sq_le_sq₀ (l2_nonneg (omittedResponse pOut pIn h))
    (mul_nonneg hc (l2_nonneg h))).mpr hl
  simpa only [mul_pow, l2_sq, normalized_four_coefficient_eq] using hs

theorem actualResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  rw [TwoOmittedOutputSplit.actualResponse_eq_omittedResponse]
  -- Only finite enumeration instances differ; the retained tuple is literal E.
  have hsum (a b : Fintype (Retained pOut → AES.Word))
      (F : (Retained pOut → AES.Word) → ℝ) :
      (letI := a; ∑ y, F y) = (letI := b; ∑ y, F y) := by
    have hab : a = b := Subsingleton.elim _ _
    cases hab
    rfl
  exact (hsum _ _ (fun y => omittedResponse pOut pIn h y ^ 2)).le.trans
    (omittedResponse_energy pOut pIn h)

end AESConcrete.TwoOmittedOutputResponseEnergy
