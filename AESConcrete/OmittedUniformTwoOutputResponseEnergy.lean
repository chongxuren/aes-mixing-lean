import AESConcrete.OmittedUniformTwoOutputEventEnergy
import AESConcrete.OmittedUniformTwoOutputSplit
import AESConcrete.OmittedUniformTwoOutputScalar
import AESConcrete.OmittedUniformTwoResponseEnergy
import AESConcrete.SevenResponse

/-!
# aggregation of actual input and output exclusion responses

All sibling OmittedUniform modules are dependencies. W uses three original
input uniforms; W0 also imposes the omitted output zero. The bare full
response of W vanishes, while all three single and all three double input-zero
responses remain. Their norms are added before squaring. The separate exact
omitted-output split then combines W with W0. The same unrestricted signed
original residual tuple h is used throughout.

Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoOutputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoOutputGeometry
open AESConcrete.OmittedUniformTwoOutputBareResponse (bareKernel)
open AESConcrete.OmittedUniformTwoOutputSplit
open AESConcrete.OmittedUniformTwoOutputScalar
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityCodeScalar (q s s_pos q_sub_one_pos)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def uniformIndexEquiv (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn ≃ Fin 3 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

def uniformThird (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 2

theorem uniformFirst_ne_second (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformSecond pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniformFirst_ne_third (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformThird pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniformSecond_ne_third (pIn : SelectedSupport 1 4) :
    uniformSecond pIn ≠ uniformThird pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniform_product (pIn : SelectedSupport 1 4) (x : AES.WordState) :
    (∏ j : SourceUniformPositions pIn, nonzeroUniform (x j.val.val)) =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) *
          nonzeroUniform (x (uniformThird pIn).val.val) := by
  have hp := (uniformIndexEquiv pIn).symm.prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (x j.val.val))
  simpa only [Fin.prod_univ_three, uniformFirst, uniformSecond, uniformThird,
    mul_assoc] using hp.symm

theorem inputWeightedResponse_eq_weighted (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h =
      WeightedResponse.weightedResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
        (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
        (fun c => c.val (uniformSecond pIn).val.val)
        (fun c => c.val (uniformThird pIn).val.val) := by
  funext y
  unfold inputWeightedResponse WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [normalizedSource, uniform_product]
  change h (residualTuple pOut pIn c) *
    (nonzeroUniform (c.val (uniformFirst pIn).val.val) *
      nonzeroUniform (c.val (uniformSecond pIn).val.val) *
        nonzeroUniform (c.val (uniformThird pIn).val.val)) * bareKernel pOut pIn y c = _
  ring

theorem rawResponse_eq_zero (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn) = 0 :=
  OmittedUniformTwoOutputBareResponse.bareResponse_eq_zero pOut pIn h

theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤ weightedC * ∑ u, h u ^ 2 := by
  have hfull : (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) y ^ 2) ≤ (0 : ℝ) ^ 2 * ∑ u, h u ^ 2 := by
    rw [rawResponse_eq_zero]
    simp
  have hsingle (j : SourceUniformPositions pIn) :
      (∑ y, WeightedResponse.zeroResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
        (bareKernel pOut pIn) (fun c => c.val j.val.val) y ^ 2) ≤
          (s * normBase) ^ 2 * ∑ u, h u ^ 2 := by
    rw [singleNorm_sq]
    exact OmittedUniformTwoOutputEventEnergy.single_zeroResponse_energy pOut pIn j h
  have hdouble (j k : SourceUniformPositions pIn) (hjk : j ≠ k) :
      (∑ y, TripleResponse.intersectionResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
        (bareKernel pOut pIn) (fun c => c.val j.val.val) (fun c => c.val k.val.val) y ^ 2) ≤
          normBase ^ 2 * ∑ u, h u ^ 2 := by
    rw [normBase_sq]
    exact OmittedUniformTwoOutputEventEnergy.double_intersectionResponse_energy pOut pIn j k hjk h
  have he := SevenResponse.weightedResponse_energy_le AES.word_card_gt_one.le
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val)
    (fun c => c.val (uniformThird pIn).val.val) h
    (OmittedUniformTwoOutputEventEnergy.triple_zero_kernel pOut pIn
      (uniformFirst pIn) (uniformSecond pIn) (uniformThird pIn)
      (uniformFirst_ne_second pIn) (uniformFirst_ne_third pIn) (uniformSecond_ne_third pIn))
    0 (s * normBase) normBase (by norm_num)
    (mul_nonneg s_pos.le normBase_nonneg) normBase_nonneg
    hfull (hsingle _) (hsingle _) (hsingle _)
    (hdouble _ _ (uniformFirst_ne_second pIn))
    (hdouble _ _ (uniformFirst_ne_third pIn))
    (hdouble _ _ (uniformSecond_ne_third pIn))
  rw [← inputWeightedResponse_eq_weighted, AES.word_card] at he
  change (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
    ((0 + 3 * (s * normBase) + 3 * normBase) ^ 2 / (q - 1) ^ 3) * ∑ u, h u ^ 2 at he
  simpa only [weighted_coefficient_eq] using he

theorem omittedResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, omittedResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  let D := WeightedResponse.normalizer AES.Word
  let d := Real.sqrt (q - 1)
  have hD : 0 ≤ D := WeightedResponse.normalizer_nonneg AES.Word
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = (q - 1) ^ 3 := by
    change WeightedResponse.normalizer AES.Word ^ 2 = (q - 1) ^ 3
    rw [WeightedResponse.normalizer_sq AES.Word AES.word_card_gt_one.le, AES.word_card]
    rfl
  have hdsq : d ^ 2 = q - 1 := Real.sq_sqrt q_sub_one_pos.le
  have hW : (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (weightedNormNumerator / D) ^ 2 * ∑ u, h u ^ 2 := by
    rw [div_pow, hDsq]
    exact inputWeightedResponse_energy pOut pIn h
  have hW0 : (∑ y, extraZeroResponse pOut pIn h y ^ 2) ≤
      (zeroOutputNormNumerator / D) ^ 2 * ∑ u, h u ^ 2 := by
    rw [div_pow, hDsq, zeroOutput_coefficient_eq]
    exact extraZeroResponse_energy pOut pIn h
  have he := OmittedUniformTwoResponseEnergy.sub_div_energy_le
    (inputWeightedResponse pOut pIn h) (extraZeroResponse pOut pIn h) h
    weightedNormNumerator zeroOutputNormNumerator D d
    weightedNormNumerator_nonneg zeroOutputNormNumerator_nonneg hD hd hW hW0
  rw [hDsq, hdsq] at he
  have hp : (q - 1) ^ 3 * (q - 1) = (q - 1) ^ 4 := by ring
  rw [hp, coefficient_eq] at he
  rw [omittedResponse_eq_split]
  exact he

theorem actualResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  rw [actualResponse_eq_omittedResponse]
  -- Counting sums do not depend on the inferred enumeration of the same type.
  have hsum (a b : Fintype (Retained pOut → AES.Word))
      (f : (Retained pOut → AES.Word) → ℝ) :
      (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
    have hab : a = b := Subsingleton.elim _ _
    cases hab
    rfl
  exact (le_of_eq (hsum _ _
    (fun y : Retained pOut → AES.Word => omittedResponse pOut pIn h y ^ 2))).trans
      (omittedResponse_energy pOut pIn h)

end AESConcrete.OmittedUniformTwoOutputResponseEnergy
