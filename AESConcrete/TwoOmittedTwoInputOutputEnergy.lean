import AESConcrete.TwoOmittedTwoInputInputEnergy
import AESConcrete.OmittedUniformTwoInputPairResponseEnergy
import AESConcrete.WeightedResidualLineCaps

/-!
Lemmas for (10,10). The exact (9,10) inputWeightedResponse interface is used;
neither its actualResponse endpoint nor physical cap is used. The double-
output plane is bounded afresh: two correlated original input U factors are
bounded at each physical state; residual and retained projections are separate
bijections. Original signed JOINT h, including zero, is retained. Constructive
fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedTwoInputOutputEnergy
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedTwoInputSource
open AESConcrete.TwoOmittedTwoInputScalar
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.UniformGraphScalar (rho)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

/-- Identity on physical states; only output inactivity is added. -/
def singleOutputRestrictionEquiv (pOut pIn : SelectedSupport 2 4) (a : Omitted pOut) :
    {x : AES.WordState // wordMixAddEquiv x a.val = 0} ≃
      OmittedUniformTwoInputRawGeometry.Code (oneZero pOut a) pIn where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi
      change maskBit (singletonMask a.val) i = true at hi
      rw [(singletonMask_bit _ _).mp hi]
      exact x.property
    · intro i hi; exact (empty_inactive pIn i hi).elim⟩
  invFun c := ⟨c.val, c.property.1 a.val ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- This is W_a with BOTH input uniforms and NO extra output uniform. -/
theorem outputZero_eq_inputWeighted (pOut pIn : SelectedSupport 2 4) (a : Omitted pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    outputZeroResponse pOut pIn a h =
      OmittedUniformTwoInputPairSource.inputWeightedResponse (oneZero pOut a) pIn h := by
  funext y
  unfold outputZeroResponse WeightedResponse.zeroResponse outputValue
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState => wordMixAddEquiv x a.val = 0),
      normalizedSource pIn h x * bareKernel pOut y x) =
      ∑ x : {x : AES.WordState // wordMixAddEquiv x a.val = 0},
        normalizedSource pIn h x.val * bareKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (singleOutputRestrictionEquiv pOut pIn a).sum_comp
    (fun c => normalizedSource pIn h c.val *
      OmittedUniformTwoInputPairSource.bareKernel (oneZero pOut a) pIn y c)

theorem outputZero_energy (pOut pIn : SelectedSupport 2 4) (a : Omitted pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputZeroResponse pOut pIn a h y ^ 2) ≤
      (outputSingleNorm / (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  rw [outputZero_eq_inputWeighted]
  have he := OmittedUniformTwoInputPairResponseEnergy.inputWeightedResponse_energy (oneZero pOut a) pIn h
  calc
    _ = ∑ y : OmittedUniformTwoInputRawGeometry.Retained (oneZero pOut a) → AES.Word,
        OmittedUniformTwoInputPairSource.inputWeightedResponse (oneZero pOut a) pIn h y ^ 2 :=
      counting_sum_instances _ _ _
    _ ≤ _ := by
      simpa only [outputSingleNorm, fullRawNorm, eventRawNorm, columnNorm,
        OmittedUniformTwoInputPairScalar.inputNorm, OmittedUniformTwoInputPairScalar.fullRawNorm,
        OmittedUniformTwoInputPairScalar.eventRawNorm, OmittedUniformTwoInputPairScalar.columnNorm] using he

abbrev DoubleOutputCode (pOut pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (maskComplement pOut.val.val.1) pIn.val.val.2

def doubleOutputCurve (pOut pIn : SelectedSupport 2 4) (c : DoubleOutputCode pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def doubleOutputResidual (pOut pIn : SelectedSupport 2 4) (c : DoubleOutputCode pOut pIn) : Residual pIn → AES.Word :=
  fun i => c.val i.val

def doubleOutputRestrictionEquiv (pOut pIn : SelectedSupport 2 4) :
    {x : AES.WordState // wordMixAddEquiv x (omittedFirst pOut).val = 0 ∧
      wordMixAddEquiv x (omittedSecond pOut).val = 0} ≃ DoubleOutputCode pOut pIn where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi
      rcases (omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) i).mp hi with ha | hb
      · rw [ha]; exact x.property.1
      · rw [hb]; exact x.property.2
    · intro i hi; exact (empty_inactive pIn i hi).elim⟩
  invFun c := ⟨c.val, by
    constructor
    · apply c.property.1
      exact (omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) _).mpr (Or.inl rfl)
    · apply c.property.1
      exact (omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) _).mpr (Or.inr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem double_output_retained_bijective (pOut pIn : SelectedSupport 2 4) :
    Function.Bijective (doubleOutputCurve pOut pIn) := by
  have hf := completion_mask_facts pOut.val.val.1 (retainedMask_size pOut)
  have hs : maskSize (maskComplement pOut.val.val.1) + maskSize pIn.val.val.2 + maskSize pOut.val.val.1 = 4 := by
    rw [OmittedUniformTwoInputRawGeometry.inputInactiveMask_size, retainedMask_size, add_zero]
    exact hf.2
  exact (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hf.1 hs).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem double_output_residual_bijective (pOut pIn : SelectedSupport 2 4) :
    Function.Bijective (doubleOutputResidual pOut pIn) := by
  have hf := completion_mask_facts pOut.val.val.1 (retainedMask_size pOut)
  have hs : maskSize (maskComplement pOut.val.val.1) + maskSize pIn.val.val.2 + maskSize pIn.val.val.1 = 4 := by
    rw [OmittedUniformTwoInputRawGeometry.inputInactiveMask_size, retainedMask_size, add_zero]
    exact hf.2
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ pIn.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

/-- The two restricted input values may correlate arbitrarily. -/
theorem original_uniform_pair_sq_le (pIn : SelectedSupport 2 4) (x : AES.WordState) :
    nonzeroUniform (x (uniformFirst pIn).val.val) ^ 2 *
      nonzeroUniform (x (uniformSecond pIn).val.val) ^ 2 ≤ 1 / (q - 1) ^ 2 := by
  have hu := WeightedResidualLineCaps.nonzeroUniform_sq_le (x (uniformFirst pIn).val.val)
  have hv := WeightedResidualLineCaps.nonzeroUniform_sq_le (x (uniformSecond pIn).val.val)
  exact (mul_le_mul hu hv (sq_nonneg _) (one_div_nonneg.mpr q_sub_one_pos.le)).trans_eq (by
    -- Normalize division before ring-style polynomial rearrangement.
    rw [div_mul_div_comm, one_mul, ← pow_two])

theorem double_output_source_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : DoubleOutputCode pOut pIn, normalizedSource pIn h c.val ^ 2) ≤
      (1 / (q - 1) ^ 2) * ∑ r, h r ^ 2 := by
  have hr := (Equiv.ofBijective (doubleOutputResidual pOut pIn)
    (double_output_residual_bijective pOut pIn)).sum_comp (fun r => h r ^ 2)
  -- Expose only the equivalence's forward restriction map before rewriting its sum.
  change (∑ c : DoubleOutputCode pOut pIn,
    h (doubleOutputResidual pOut pIn c) ^ 2) = ∑ r, h r ^ 2 at hr
  calc
    _ ≤ ∑ c : DoubleOutputCode pOut pIn, h (doubleOutputResidual pOut pIn c) ^ 2 * (1 / (q - 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      rw [normalizedSource_eq_two, mul_pow, mul_pow]
      calc
        _ = h (doubleOutputResidual pOut pIn c) ^ 2 *
            (nonzeroUniform (c.val (uniformFirst pIn).val.val) ^ 2 *
              nonzeroUniform (c.val (uniformSecond pIn).val.val) ^ 2) := by
          -- h's literal restriction and doubleOutputResidual are definitionally the same.
          unfold doubleOutputResidual
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (original_uniform_pair_sq_le pIn c.val) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hr]; ring

theorem outputIntersection_eq_response (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    outputIntersectionResponse pOut pIn h = IndexedTripleEnergy.response
      (residualMatrix AES.wordSuperboxKernel 0) (doubleOutputCurve pOut pIn)
      (fun c => normalizedSource pIn h c.val) := by
  funext y
  unfold outputIntersectionResponse TripleResponse.intersectionResponse outputValue
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState =>
      wordMixAddEquiv x (omittedFirst pOut).val = 0 ∧ wordMixAddEquiv x (omittedSecond pOut).val = 0),
      normalizedSource pIn h x * bareKernel pOut y x) =
      ∑ x : {x : AES.WordState // wordMixAddEquiv x (omittedFirst pOut).val = 0 ∧
        wordMixAddEquiv x (omittedSecond pOut).val = 0},
        normalizedSource pIn h x.val * bareKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (doubleOutputRestrictionEquiv pOut pIn).sum_comp
    (fun c => normalizedSource pIn h c.val * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (doubleOutputCurve pOut pIn c i))

theorem outputIntersection_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputIntersectionResponse pOut pIn h y ^ 2) ≤
      (eventRawNorm / (q - 1)) ^ 2 * ∑ r, h r ^ 2 := by
  rw [outputIntersection_eq_response]
  have he := TwoOmittedTwoInputInputEnergy.response_energy_of_bijective pOut
    (doubleOutputCurve pOut pIn) (double_output_retained_bijective pOut pIn)
    (fun c => normalizedSource pIn h c.val)
  exact he.trans ((mul_le_mul_of_nonneg_left (double_output_source_energy pOut pIn h)
    (pow_nonneg (UniformGraphScalar.rho_nonneg) _)).trans_eq (by
      rw [event_energy_coefficient_eq, div_pow]
      ring))
end AESConcrete.TwoOmittedTwoInputOutputEnergy
