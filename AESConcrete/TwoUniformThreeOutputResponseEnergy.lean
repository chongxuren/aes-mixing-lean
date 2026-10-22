import AESConcrete.TwoUniformThreeOutputFullEnergy
import AESConcrete.TwoUniformThreeOutputEventEnergy
import AESConcrete.TwoUniformThreeOutputScalar
import AESConcrete.WeightedThreeOutputCaps
import AESConcrete.TripleResponse

/-!
# Exact two-weight expansion on the actual three-output code

The support indices are (11,10). Both original input uniform labels occur
exactly once. The full response, two original input-zero planes and their
intersection line all preserve one arbitrary signed residual-pair amplitude h.
Triangle aggregation precedes squaring; the intersection is retained. The
comparator is the original sum of h^2, not a replicated or conditioned source
energy. Source normalization, selected energy and physical aggregation remain
separate.

Constructive independent-retained-key AES10/14/16 with whitening, omitted
final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoUniformThreeOutputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoUniformThreeOutputGeometry
open AESConcrete.TwoUniformThreeOutputScalar
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def uniformIndexEquiv (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 2 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

theorem uniformFirst_ne_second (pIn : SelectedSupport 2 4) :
    uniformFirst pIn ≠ uniformSecond pIn := by
  intro he
  have hf : (0 : Fin 2) = 1 := by
    simpa only [uniformFirst, uniformSecond, Equiv.apply_symm_apply] using
      congrArg (uniformIndexEquiv pIn) he
  exact (by decide : (0 : Fin 2) ≠ 1) hf

theorem uniform_product (pIn : SelectedSupport 2 4) (x : AES.WordState) :
    WeightedThreeOutputCaps.uniformWeight pIn x =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) := by
  have hp := (uniformIndexEquiv pIn).symm.prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (x j.val.val))
  simpa only [WeightedThreeOutputCaps.uniformWeight,
    Fin.prod_univ_two, uniformFirst, uniformSecond] using hp.symm

def residualKernel (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i)
      (AESConcrete.WordCrossZero.wordMixAddEquiv c.val i.val)

def response (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  TripleResponse.weightedResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (residualKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val)

/-- The generic normalized-source response has exactly these two original weights. -/
theorem jointResponse_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedThreeOutputCaps.jointResponse pOut pIn h = response pOut pIn h := by
  funext y
  unfold WeightedThreeOutputCaps.jointResponse IndexedTripleEnergy.response
    response TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [WeightedThreeOutputCaps.weightedAmplitude, uniform_product]
  change h (residualTuple pOut pIn c) *
    (nonzeroUniform (c.val (uniformFirst pIn).val.val) *
      nonzeroUniform (c.val (uniformSecond pIn).val.val)) * residualKernel pOut pIn y c = _
  ring

theorem rawFull_response_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) =
        TwoUniformThreeOutputFullEnergy.rawFullResponse pOut pIn h := rfl

def normBase : ℝ := Real.sqrt baseSquared

theorem normBase_nonneg : 0 ≤ normBase := Real.sqrt_nonneg _

theorem normBase_sq : normBase ^ 2 = baseSquared := Real.sq_sqrt baseSquared_nonneg

variable (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)

theorem full_response_safe (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) y ^ 2) ≤ fullNorm normBase ^ 2 * ∑ u, h u ^ 2 := by
  rw [rawFull_response_eq, fullNorm_sq normBase normBase_sq]
  exact TwoUniformThreeOutputFullEnergy.rawFullResponse_energy pOut pIn h

theorem single_response_safe (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
        eventNorm normBase ^ 2 * ∑ v, h v ^ 2 := by
  rw [eventNorm_sq normBase normBase_sq]
  exact TwoUniformThreeOutputEventEnergy.single_zeroResponse_energy pOut pIn u h

theorem intersection_response_safe (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
        eventNorm normBase ^ 2 * ∑ u, h u ^ 2 :=
  (TwoUniformThreeOutputEventEnergy.double_intersectionResponse_energy
    pOut pIn (uniformFirst pIn) (uniformSecond pIn) (uniformFirst_ne_second pIn) h).trans
      (mul_le_mul_of_nonneg_right
        (intersection_energy_le_eventNorm_sq normBase normBase_sq)
        (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

/-- Add the four norms before squaring, with denominator exactly (q-1)^2. -/
theorem response_energy (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  have he := TripleResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (residualKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val) h
    (fullNorm normBase) (eventNorm normBase) (eventNorm normBase) (eventNorm normBase)
    (fullNorm_nonneg normBase normBase_nonneg)
    (eventNorm_nonneg normBase normBase_nonneg)
    (eventNorm_nonneg normBase normBase_nonneg)
    (eventNorm_nonneg normBase normBase_nonneg)
    (full_response_safe pOut pIn h)
    (single_response_safe pOut pIn (uniformFirst pIn) h)
    (single_response_safe pOut pIn (uniformSecond pIn) h)
    (intersection_response_safe pOut pIn h)
  rw [DoubleUniformFourierEnergy.word_card_real,
    four_coefficient_eq normBase normBase_sq] at he
  exact he

theorem joint_response_energy (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedThreeOutputCaps.jointResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  rw [jointResponse_eq]
  exact response_energy pOut pIn h

end AESConcrete.TwoUniformThreeOutputResponseEnergy
