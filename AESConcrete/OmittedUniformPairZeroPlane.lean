import AESConcrete.OmittedUniformTwoInputPairSplit
import AESConcrete.OmittedUniformPairEventEnergy
import AESConcrete.WeightedResidualLineCaps

/-!
# Same-source extra-output-zero plane energy for (9,10)

PairSource, PairSplit and the raw modules supply the source interfaces. W0 is
PairSplit.extraZeroResponse itself: the SAME arbitrary signed joint residual-
pair h and BOTH original physical nonzero-uniform input factors, restricted to
the actual extra-output-zero plane. The retained pair and the original
residual pair each parametrize this plane. Pointwise bounds on the two
physical factors allow arbitrary correlations.

No h factorization, centering, zero-pair-value or desired-bound premise is
used. Constructive fixed AES10/14/16, independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct reference.

No scalar comparison, selected-minor estimate or physical aggregation is
supplied here.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformPairZeroPlane
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.OmittedUniformTwoInputPairSource (normalizedSource uniformWeight)
open AESConcrete.OmittedUniformTwoInputPairSplit (ExtraZeroCode extraZeroResponse)
open AESConcrete.ShortenedWeightedGeometry (graphEquiv)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.UniformGraphScalar (rho)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- PairSplit's actual extra-zero code, with unchanged physical output labels. -/
def planeCurve (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : ExtraZeroCode pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

/-- The complete original residual input tuple; the zero pair is retained. -/
def planeResidualTuple (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (c : ExtraZeroCode pOut pIn) : Residual pIn → AES.Word :=
  fun i => c.val i.val

theorem plane_retained_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) : Function.Bijective (planeCurve pOut pIn) := by
  have hf := OmittedUniformTwoOutputSplit.completion_mask_facts
    pOut.val.val.1 (retainedMask_size pOut)
  have hs : maskSize (maskComplement pOut.val.val.1) + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 = 4 := by
    rw [inputInactiveMask_size, retainedMask_size, add_zero]
    exact hf.2
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _ hf.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem plane_residual_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) :
    Function.Bijective (planeResidualTuple pOut pIn) := by
  have hf := OmittedUniformTwoOutputSplit.completion_mask_facts
    pOut.val.val.1 (retainedMask_size pOut)
  have hs : maskSize (maskComplement pOut.val.val.1) + maskSize pIn.val.val.2 +
      maskSize pIn.val.val.1 = 4 := by
    rw [inputInactiveMask_size, residualMask_size, add_zero]
    exact hf.2
  exact (RestrictedMDSCoordinates.input_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pIn.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem plane_joint_amplitude_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : ExtraZeroCode pOut pIn, h (planeResidualTuple pOut pIn c) ^ 2) =
      ∑ u, h u ^ 2 :=
  (Equiv.ofBijective _ (plane_residual_bijective pOut pIn)).sum_comp
    (fun u => h u ^ 2)

/-- Both original input weights are bounded at the same physical state.
No product distribution or independence of their restrictions is asserted. -/
theorem uniformWeight_sq_le (pIn : SelectedSupport 2 4) (x : AES.WordState) :
    uniformWeight pIn x ^ 2 ≤ 1 / (q - 1) ^ 2 := by
  unfold uniformWeight
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _j : SourceUniformPositions pIn, (1 / (q - 1) : ℝ) :=
      Finset.prod_le_prod (fun j _ => sq_nonneg (nonzeroUniform (x j.val.val)))
        (fun j _ => WeightedResidualLineCaps.nonzeroUniform_sq_le (x j.val.val))
    _ = 1 / (q - 1) ^ 2 := by
      have hc := sourceUniformPositions_card pIn
      simp only [← Nat.card_eq_fintype_card] at hc
      simp only [Finset.prod_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, hc, div_pow, one_pow]

/-- Restrict the SAME normalized source, keeping both original physical factors. -/
theorem plane_normalizedSource_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : ExtraZeroCode pOut pIn, normalizedSource pIn h c.val ^ 2) ≤
      (∑ u, h u ^ 2) / (q - 1) ^ 2 := by
  calc
    _ ≤ ∑ c : ExtraZeroCode pOut pIn,
        h (planeResidualTuple pOut pIn c) ^ 2 * (1 / (q - 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      rw [OmittedUniformTwoInputPairSplit.normalizedSource_on_extraZeroCode, mul_pow]
      exact mul_le_mul_of_nonneg_left (uniformWeight_sq_le pIn c.val)
        (sq_nonneg (h (planeResidualTuple pOut pIn c)))
    _ = (∑ c : ExtraZeroCode pOut pIn,
        h (planeResidualTuple pOut pIn c) ^ 2) * (1 / (q - 1) ^ 2) :=
      (Finset.sum_mul _ _ _).symm
    _ = (∑ u, h u ^ 2) / (q - 1) ^ 2 := by
      rw [plane_joint_amplitude_energy]
      ring

/-- PairSplit's exact W0 response, rather than a substitute source or plane. -/
theorem extraZeroResponse_eq_response (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    extraZeroResponse pOut pIn h =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (planeCurve pOut pIn) (fun c => normalizedSource pIn h c.val) := rfl

/-- Public endpoint: both retained tensor factors and both original input weights. -/
theorem extraZeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSplit.extraZeroResponse pOut pIn h y ^ 2) ≤
      rho ^ 4 * (∑ u, h u ^ 2) / (q - 1) ^ 2 := by
  rw [extraZeroResponse_eq_response]
  have he := OmittedUniformPairEventEnergy.response_energy_of_bijective pOut
    (planeCurve pOut pIn) (plane_retained_bijective pOut pIn)
    (fun c => normalizedSource pIn h c.val)
  calc
    _ ≤ rho ^ 4 * ∑ c : ExtraZeroCode pOut pIn, normalizedSource pIn h c.val ^ 2 := he
    _ ≤ rho ^ 4 * ((∑ u, h u ^ 2) / (q - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (plane_normalizedSource_energy pOut pIn h)
        (pow_nonneg (UniformGraphScalar.rho_nonneg) _)
    _ = rho ^ 4 * (∑ u, h u ^ 2) / (q - 1) ^ 2 := by ring

end AESConcrete.OmittedUniformPairZeroPlane
