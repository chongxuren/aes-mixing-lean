import AESConcrete.TwoOmittedThreeInputSplit

/-!
# same-source response energy for cell (10,7)

Raw W has numerator (3s+1)a. The two one-zero responses have (3s+3)a, and the
double-zero response has (s+3)a, all over the original input normalizer d³.
The output four-term triangle yields (10s+10)a/(D*d³). Every estimate uses the
same signed h. The (9,7) inputWeightedResponse and extraZeroResponse
are used at their exact types. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedThreeInputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedThreeInputGeometry (Retained Residual)
open AESConcrete.TwoOmittedThreeInputResponse (inputWeightedResponse)
open AESConcrete.TwoOmittedThreeInputSource
open AESConcrete.TwoOmittedThreeInputSplit (omittedResponse actualResponse)
open AESConcrete.TwoOmittedThreeInputScalar
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem oneZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, oneZeroResponse pOut pIn a h y ^ 2) ≤
      (oneZeroNormNumerator / inputNormalizer) ^ 2 * ∑ r, h r ^ 2 := by
  rw [oneZero_coefficient_eq]
  exact OmittedUniformTwoOutputResponseEnergy.inputWeightedResponse_energy (oneZero pOut a) pIn h

theorem twoZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, twoZeroResponse pOut pIn h y ^ 2) ≤
      (twoZeroNormNumerator / inputNormalizer) ^ 2 * ∑ r, h r ^ 2 := by
  rw [twoZero_coefficient_eq]
  exact OmittedUniformTwoOutputSplit.extraZeroResponse_energy
    (oneZero pOut (omittedFirst pOut)) pIn h

theorem omittedResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, omittedResponse pOut pIn h y ^ 2) ≤ C * ∑ r, h r ^ 2 := by
  have ha := div_nonneg rawNormNumerator_nonneg inputNormalizer_nonneg
  have hb := div_nonneg oneZeroNormNumerator_nonneg inputNormalizer_nonneg
  have hc := div_nonneg twoZeroNormNumerator_nonneg inputNormalizer_nonneg
  have hl := TripleResponse.four_response_l2_le
    (inputWeightedResponse pOut pIn h)
    (oneZeroResponse pOut pIn (omittedFirst pOut) h)
    (oneZeroResponse pOut pIn (omittedSecond pOut) h) (twoZeroResponse pOut pIn h) h
    (rawNormNumerator / inputNormalizer) (oneZeroNormNumerator / inputNormalizer)
    (oneZeroNormNumerator / inputNormalizer) (twoZeroNormNumerator / inputNormalizer) (q - 1)
    ha hb hb hc (TwoOmittedThreeInputResponse.inputWeightedResponse_energy pOut pIn h)
    (oneZeroResponse_energy pOut pIn (omittedFirst pOut) h)
    (oneZeroResponse_energy pOut pIn (omittedSecond pOut) h)
    (twoZeroResponse_energy pOut pIn h)
  rw [abs_of_nonneg q_sub_one_pos.le, ← TwoOmittedThreeInputSplit.omittedResponse_eq_split] at hl
  have hn : 0 ≤ (rawNormNumerator / inputNormalizer + oneZeroNormNumerator / inputNormalizer +
      oneZeroNormNumerator / inputNormalizer + twoZeroNormNumerator / inputNormalizer) / (q - 1) :=
    div_nonneg (add_nonneg (add_nonneg (add_nonneg ha hb) hb) hc) q_sub_one_pos.le
  have hs := (sq_le_sq₀ (l2_nonneg (omittedResponse pOut pIn h))
    (mul_nonneg hn (l2_nonneg h))).mpr hl
  simpa only [mul_pow, l2_sq, normalized_four_coefficient_eq] using hs

theorem actualResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ r, h r ^ 2 := by
  rw [TwoOmittedThreeInputSplit.actualResponse_eq_omittedResponse]
  have hsum (a b : Fintype (Retained pOut → AES.Word))
      (F : (Retained pOut → AES.Word) → ℝ) :
      (letI := a; ∑ y, F y) = (letI := b; ∑ y, F y) := by
    have he : a = b := Subsingleton.elim _ _
    cases he
    rfl
  exact (hsum _ _ (fun y => omittedResponse pOut pIn h y ^ 2)).le.trans
    (omittedResponse_energy pOut pIn h)

end AESConcrete.TwoOmittedThreeInputResponseEnergy
