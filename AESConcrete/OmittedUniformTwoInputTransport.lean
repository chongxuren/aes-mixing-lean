import AESConcrete.OmittedUniformTwoInputGeometry
import AESConcrete.OmittedUniformTwoOutputEventEnergy
import AESConcrete.WeightedResidualLineCaps
import AESConcrete.TripleResponse

/-!
# Exact original-amplitude transports for the (9,6) input plane

W has two, not three, normalized input uniform factors. The original input
zero has unit delta weight on Code. A is the completed single event; B and C
are the completed double events. D vanishes by the completed triple-zero
kernel. All terms have the same arbitrary signed original residual-tuple h,
including h(0). Constructive fixed AES10/14/16 only.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputTransport
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputGeometry
open AESConcrete.NonzeroUniformGraphCap (zeroUnit nonzeroUniform)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def normalizedSource (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  WeightedResidualLineCaps.normalizedSource pIn h

theorem normalizedSource_energy (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 :=
  WeightedResidualLineCaps.normalizedSource_energy pIn h

theorem normalizedSource_on_code (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) :
    normalizedSource pIn h c.val = h (residualTuple pOut pIn c) *
      WeightedResidualLineCaps.uniformWeight pIn c.val := by
  rw [normalizedSource, WeightedResidualLineCaps.normalizedSource_eq]
  have hp : (∏ i : MultiUniformExpansion.InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (c.val i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hz := c.property.2 i.val.val i.property
    simp [zeroUnit, supportConstant, identityKernel, hz]
  rw [hp, mul_one]
  rfl

theorem uniformWeight_eq_two (pIn : SelectedSupport 1 3) (x : AES.WordState) :
    WeightedResidualLineCaps.uniformWeight pIn x =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) := by
  have he := (uniformIndexEquiv pIn).symm.prod_comp
    (fun i : SourceUniformPositions pIn => nonzeroUniform (x i.val.val))
  simpa only [Fin.prod_univ_two,
    OmittedUniformTwoInputGeometry.uniformFirst, OmittedUniformTwoInputGeometry.uniformSecond,
    WeightedResidualLineCaps.uniformWeight] using he.symm

def rawResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (bareKernel pOut pIn)

theorem rawResponse_eq_event (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    rawResponse pOut pIn h = OmittedUniformTwoOutputEventGeometry.eventResponse
      pOut (completeInput pIn)
      (OmittedUniformTwoOutputEventGeometry.singleMask (completedInactive pIn)) h := by
  funext y
  unfold rawResponse WeightedResponse.rawResponse
    OmittedUniformTwoOutputEventGeometry.eventResponse IndexedTripleEnergy.response
  exact (planeEventEquiv pOut pIn).sum_comp
    (fun c => h (OmittedUniformTwoOutputEventGeometry.eventResidualTuple
      pOut (completeInput pIn) _ c) * ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i)
          (OmittedUniformTwoOutputEventGeometry.eventCurve pOut (completeInput pIn) _ c i))

def additionalResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (t : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn,
    if OmittedUniformTwoOutputEventGeometry.inputConditions t c.val then
      h (residualTuple pOut pIn c) * bareKernel pOut pIn y c else 0

theorem additionalResponse_eq_event (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (t : Fin 16) (h : (Residual pIn → AES.Word) → ℝ) :
    additionalResponse pOut pIn t h = OmittedUniformTwoOutputEventGeometry.eventResponse
      pOut (completeInput pIn) (maskUnion pIn.val.val.2 t) h := by
  funext y
  unfold additionalResponse OmittedUniformTwoOutputEventGeometry.eventResponse
    IndexedTripleEnergy.response
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn =>
      OmittedUniformTwoOutputEventGeometry.inputConditions t c.val),
      h (residualTuple pOut pIn c) * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn //
      OmittedUniformTwoOutputEventGeometry.inputConditions t c.val},
      h (residualTuple pOut pIn c.val) * bareKernel pOut pIn y c.val from
        Finset.sum_subtype _ (by simp) _]
  exact (conditionedEventEquiv pOut pIn t).sum_comp
    (fun c => h (OmittedUniformTwoOutputEventGeometry.eventResidualTuple
      pOut (completeInput pIn) _ c) * ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i)
          (OmittedUniformTwoOutputEventGeometry.eventCurve pOut (completeInput pIn) _ c i))

theorem zeroResponse_eq_event (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.zeroResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) =
    OmittedUniformTwoOutputEventGeometry.eventResponse pOut (completeInput pIn)
      (OmittedUniformTwoOutputEventGeometry.doubleMask
        (completedInactive pIn) (completedUniform pIn u)) h := by
  calc
    _ = additionalResponse pOut pIn
        (OmittedUniformTwoOutputEventGeometry.singleMask (completedUniform pIn u)) h := by
      funext y
      simp only [WeightedResponse.zeroResponse, additionalResponse,
        OmittedUniformTwoOutputEventGeometry.single_conditions_iff, completedUniform]
    _ = _ := by
      rw [additionalResponse_eq_event,
        OmittedUniformTwoOutputEventGeometry.doubleMask, completed_singleMask]

theorem intersectionResponse_eq_zero (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) = 0 := by
  funext y
  unfold TripleResponse.intersectionResponse
  apply Finset.sum_eq_zero
  intro c _
  split_ifs with hz
  · have hK : bareKernel pOut pIn y c = 0 := by
      exact OmittedUniformTwoOutputEventEnergy.triple_zero_kernel pOut (completeInput pIn)
        (completedInactive pIn) (completedUniform pIn u) (completedUniform pIn v)
        (completedInactive_ne_uniform pIn u) (completedInactive_ne_uniform pIn v)
        (fun he => huv ((completedUniform_injective pIn) he)) y (baseCode pOut pIn c)
        (c.property.2 _ (inactiveLabel_mem pIn)) hz.1 hz.2
    rw [hK, mul_zero]
  · rfl

/-- W keeps the original inactive delta and precisely the original two uniforms. -/
def inputWeightedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val * bareKernel pOut pIn y c

theorem inputWeightedResponse_eq_two (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = TripleResponse.weightedResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) := by
  funext y
  unfold inputWeightedResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [normalizedSource_on_code, uniformWeight_eq_two]
  ring

/-- The original inactive delta adds no factor to the input normalizer q-1. -/
theorem inputWeightedResponse_eq_three (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputWeightedResponse pOut pIn h = fun y =>
      (rawResponse pOut pIn h y - WeightedResponse.zeroResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
        (fun c => c.val (uniformFirst pIn).val.val) y - WeightedResponse.zeroResponse
        (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
        (fun c => c.val (uniformSecond pIn).val.val) y) / (ActivityCodeScalar.q - 1) := by
  rw [inputWeightedResponse_eq_two, TripleResponse.weightedResponse_eq_four]
  have hD := intersectionResponse_eq_zero pOut pIn
    (uniformFirst pIn) (uniformSecond pIn) (uniformFirst_ne_second pIn) h
  have hn := TripleResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one)
  rw [DoubleUniformFourierEnergy.word_card_real] at hn
  simp only [hD, Pi.zero_apply, add_zero, hn, rawResponse]

end AESConcrete.OmittedUniformTwoInputTransport
