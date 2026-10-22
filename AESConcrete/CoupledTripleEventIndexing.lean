import AESConcrete.CoupledTripleEventEnergy

/-!
# Exact response transport for the two original joint-triple exclusions

This module transports finite sums only; it introduces no new event order,
response estimate, normalization factor or physical cap.

The input constraint is the ORIGINAL scalar `uv.2=0`. The output constraint is
the qualified `CoupledTripleMinorResponse.omittedValue=0`. Their named
physical source subtypes are exactly inputEvent, outputEvent and
intersectionEvent. The same arbitrary signed JOINT residual-triple h is used
pointwise throughout, with all zero source values preserved. No factorization,
axis-zero, positivity, centering or endpoint cancellation is assumed.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleEventIndexing
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber (ResidualPositions RetainedPositions)
open AESConcrete.CoupledTripleSource (SourceWord sourceWordEquiv)
open AESConcrete.CoupledTripleMinorResponse (Retained residualKernel retainedMap)
open AESConcrete.CoupledTripleEventGeometry
open AESConcrete.CoupledTripleEventEnergy (sourceEventResponse)

attribute [local instance] Classical.propDecidable

set_option maxRecDepth 100000
variable (pOut pIn : SelectedSupport 3 4)

/-- Align the actual source/code curve pointwise before transporting its sum. -/
theorem eventSource_retained_apply (s : Events pOut pIn) (uv : EventSource s)
    (i : RetainedPositions pOut) :
    eventRetainedHom s (eventSourceEquiv s uv) i = retainedMap pOut pIn uv.val i := by
  rw [eventRetainedHom_apply]
  rfl

/-- Raw response on precisely the selected original source subtype. -/
theorem sourceEventResponse_eq_subtype_sum (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    sourceEventResponse s h y = ∑ uv : EventSource s,
      h uv.val.1 * residualKernel pOut pIn y uv.val := by
  unfold sourceEventResponse IndexedTripleEnergy.response
  apply Finset.sum_congr rfl
  intro uv _
  unfold residualKernel
  simp_rw [eventSource_retained_apply pOut pIn]

/-- A conditional sum on the complete original scalar source, without weights. -/
def conditionalResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ uv : SourceWord pIn, if eventConditions s (sourceWordEquiv pIn uv)
    then h uv.1 * residualKernel pOut pIn y uv else 0

/-- Exact full-source/subtype identity, with no injectivity or energy premise. -/
theorem conditionalResponse_eq_sourceEventResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    conditionalResponse pOut pIn s h = sourceEventResponse s h := by
  classical
  funext y
  rw [sourceEventResponse_eq_subtype_sum pOut pIn s h y]
  unfold conditionalResponse
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The named input event fixes the original scalar complement, not a new leg. -/
theorem input_condition_iff (uv : SourceWord pIn) :
    eventConditions (inputEvent pOut pIn) (sourceWordEquiv pIn uv) ↔ uv.2 = 0 :=
  input_eventConditions_source_iff (pOut := pOut) (pIn := pIn) uv.1 uv.2

/-- Keep the omitted-output value fully qualified to avoid a different source API. -/
theorem output_condition_iff (uv : SourceWord pIn) :
    eventConditions (outputEvent pOut pIn) (sourceWordEquiv pIn uv) ↔
      CoupledTripleMinorResponse.omittedValue pOut pIn uv = 0 :=
  output_eventConditions_source_iff (pOut := pOut) (pIn := pIn) uv.1 uv.2

/-- Both actual constraints survive at the original plane intersection. -/
theorem intersection_condition_iff (uv : SourceWord pIn) :
    eventConditions (intersectionEvent pOut pIn) (sourceWordEquiv pIn uv) ↔
      uv.2 = 0 ∧ CoupledTripleMinorResponse.omittedValue pOut pIn uv = 0 :=
  double_eventConditions_source_iff (intersectionEvent pOut pIn)
    (intersectionEvent_card pOut pIn) uv.1 uv.2

theorem input_zeroResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2) =
        sourceEventResponse (inputEvent pOut pIn) h := by
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn]
  funext y
  unfold WeightedResponse.zeroResponse conditionalResponse
  simp_rw [input_condition_iff pOut pIn]

theorem output_zeroResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (CoupledTripleMinorResponse.omittedValue pOut pIn) =
        sourceEventResponse (outputEvent pOut pIn) h := by
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn]
  funext y
  unfold WeightedResponse.zeroResponse conditionalResponse
  simp_rw [output_condition_iff pOut pIn]

theorem intersectionResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2)
      (CoupledTripleMinorResponse.omittedValue pOut pIn) =
        sourceEventResponse (intersectionEvent pOut pIn) h := by
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn]
  funext y
  unfold TripleResponse.intersectionResponse conditionalResponse
  simp_rw [intersection_condition_iff pOut pIn]

end AESConcrete.CoupledTripleEventIndexing
