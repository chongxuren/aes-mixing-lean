import AESConcrete.TripleUniformEventIndexing
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# actual selected-minor response for one residual and three uniforms

The full four-word source is reindexed by its actual equivalence. Its three
original uniform-input factors and the omitted-output factor occur once each.
The resulting retained minor is exactly FourteenResponse.weightedResponse with
the original physical event functions. The retained triple is not used as an
injective parameterization of the unrestricted four-word source.

Pointwise minor and selected-tensor identities precede the exact counting
energy transport. The extracted signed amplitude retains its source identity,
zero and zero-sum properties and exact input energy, although the response
identities themselves work for arbitrary signed amplitudes.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference pairs and the fixed AES 10/14/16 target remain
unchanged. No physical cap, return or complete AES theorem is asserted.

Energy bounds and physical support aggregation are separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource
open AESConcrete.TripleUniformFullResponse
  (SourceWord Retained sourceWordEquiv retainedMap omittedValue residualKernel)
open AESConcrete.TripleUniformEventIndexing
  (uniformIndexEquiv eventValue eventValue_zero eventValue_succ all_event_values_zero_iff)
open AESConcrete.ThreeActiveGeometry (omittedLabel omittedLabel_not_retained)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction
  (minorResponse minorKernel nonzeroWeight coordinateKernel_rank_one_minor)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)

attribute [local instance] Classical.propDecidable

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev Omitted (pOut : SelectedSupport 3 4) :=
  GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1

def omittedOther (pOut : SelectedSupport 3 4) : Omitted pOut :=
  ⟨omittedLabel pOut, omittedLabel_not_retained pOut⟩

theorem omittedOther_unique (pOut : SelectedSupport 3 4) (j : Omitted pOut) :
    j = omittedOther pOut :=
  Subtype.ext (TripleUniformFullResponse.omittedLabel_eq_of_not_retained pOut j.val j.property)

theorem omitted_product (pOut : SelectedSupport 3 4) (x : AES.WordState) :
    (∏ j : Omitted pOut, nonzeroUniform (x j.val)) =
      nonzeroUniform (x (omittedLabel pOut)) := by
  rw [Finset.prod_eq_single (omittedOther pOut)]
  · rfl
  · intro j _ hj
    exact (hj (omittedOther_unique pOut j)).elim
  · simp

theorem omittedWeight_eq (pOut : SelectedSupport 3 4) (j : Omitted pOut) (x : AES.Word) :
    nonzeroWeight (selectedRetained 3 4 pOut) (selectedZeros 3 4 pOut) j x =
      nonzeroUniform x := by
  have hz := RetainedGraphMasks.fullActive_selectedZeros_empty 3 pOut j.val
  simp only [nonzeroWeight, if_neg hz]

/-- Exact source enumeration; there is no inactive-input restriction. -/
theorem full_source_sum (pIn : SelectedSupport 1 4) (F : AES.WordState → ℝ) :
    (∑ x, F x) = ∑ uv : SourceWord pIn, F (source pIn uv.1 uv.2) :=
  ((sourceWordEquiv pIn).sum_comp F).symm

theorem uniform_product (pIn : SelectedSupport 1 4)
    (v : SourceUniformPositions pIn → AES.Word) :
    (∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) =
      nonzeroUniform (v (uniformIndexEquiv pIn 0)) *
      nonzeroUniform (v (uniformIndexEquiv pIn 1)) *
      nonzeroUniform (v (uniformIndexEquiv pIn 2)) := by
  have hp := (uniformIndexEquiv pIn).prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (v j))
  simpa only [Fin.prod_univ_three, mul_assoc] using hp.symm

/-- The physical event order is omitted output, then the three original inputs. -/
theorem event_weight_product (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn) :
    nonzeroUniform (eventValue pOut pIn 0 uv) *
      nonzeroUniform (eventValue pOut pIn 1 uv) *
      nonzeroUniform (eventValue pOut pIn 2 uv) *
      nonzeroUniform (eventValue pOut pIn 3 uv) =
      (∏ j : SourceUniformPositions pIn, nonzeroUniform (uv.2 j)) *
        nonzeroUniform (omittedValue pOut pIn uv) := by
  have h1 : eventValue pOut pIn 1 uv = uv.2 (uniformIndexEquiv pIn 0) :=
    eventValue_succ pOut pIn 0 uv
  have h2 : eventValue pOut pIn 2 uv = uv.2 (uniformIndexEquiv pIn 1) :=
    eventValue_succ pOut pIn 1 uv
  have h3 : eventValue pOut pIn 3 uv = uv.2 (uniformIndexEquiv pIn 2) :=
    eventValue_succ pOut pIn 2 uv
  rw [eventValue_zero, h1, h2, h3, uniform_product]
  ring

def response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  FourteenResponse.weightedResponse (fun uv : SourceWord pIn => h uv.1)
    (residualKernel pOut pIn) (eventValue pOut pIn)

/-- Three original source factors and the omitted-output factor occur once. -/
theorem response_eq_source_weights (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (y : Retained pOut → AES.Word) :
    response pOut pIn h y = ∑ uv : SourceWord pIn,
      (h uv.1 * ∏ j : SourceUniformPositions pIn, nonzeroUniform (uv.2 j)) *
        nonzeroUniform (omittedValue pOut pIn uv) * residualKernel pOut pIn y uv := by
  unfold response FourteenResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro uv _
  calc
    _ = h uv.1 * (nonzeroUniform (eventValue pOut pIn 0 uv) *
        nonzeroUniform (eventValue pOut pIn 1 uv) *
        nonzeroUniform (eventValue pOut pIn 2 uv) *
        nonzeroUniform (eventValue pOut pIn 3 uv)) * residualKernel pOut pIn y uv := by ring
    _ = _ := by rw [event_weight_product]; ring

/-- Pointwise retained-minor identity, using the full four-word source sum. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) :
    minorResponse (selectedRetained 3 4 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 3 4 pOut) (selectedZeros 3 4 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) = response pOut pIn h := by
  unfold selectedRetained
  funext y
  unfold minorResponse action
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  rw [full_source_sum pIn _, response_eq_source_weights]
  apply Finset.sum_congr rfl
  intro uv _
  rw [hsource]
  unfold minorKernel
  have ho : (∏ j : Omitted pOut,
      nonzeroWeight (selectedRetained 3 4 pOut) (selectedZeros 3 4 pOut) j
        (wordMixAddEquiv (source pIn uv.1 uv.2) j.val)) =
      nonzeroUniform (omittedValue pOut pIn uv) := by
    simp_rw [omittedWeight_eq]
    exact omitted_product pOut _
  unfold selectedRetained at ho
  rw [counting_prod_instances (X := Omitted pOut) _ inferInstance, ho]
  unfold residualKernel retainedMap restrictCoordinates
  rw [counting_prod_instances (X := Retained pOut) _ inferInstance]
  ring

/-- The full output is the retained response times its one unit output leg. -/
theorem selectedStep_action_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j))
    (y : AES.WordState) :
    action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y =
      nonzeroUniform (y (omittedLabel pOut)) *
        response pOut pIn h (fun i : Retained pOut => y i.val) := by
  rw [ActivityMinorInput.selectedStepKernel_action, selectedWordTensor_rank_one,
    coordinateKernel_rank_one_minor (selectedRetained 3 4 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 3 4 pOut) (selectedZeros 3 4 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) y,
    minorResponse_eq pOut pIn G h hsource]
  congr 1
  have ho : (∏ j : Omitted pOut,
      nonzeroWeight (selectedRetained 3 4 pOut) (selectedZeros 3 4 pOut) j (y j.val)) =
      nonzeroUniform (y (omittedLabel pOut)) := by
    simp_rw [omittedWeight_eq]
    exact omitted_product pOut y
  unfold selectedRetained at ho ⊢
  rw [counting_prod_instances (X := Omitted pOut) _ inferInstance]
  exact ho

/-- Exact counting energy transport through the unit omitted-output leg. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

/-- The actual extracted amplitude keeps its source constraints and exact energy. -/
theorem selected_component_response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      h 0 = 0 ∧ (∑ u, h u) = 0 ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) pIn.val f (source pIn u v) =
        h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) ∧
      ((∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2) = ∑ u, h u ^ 2) ∧
      (∀ y : AES.WordState,
        action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
          (supportIndexComponent (0 : AES.Word) pIn.val f) y =
          nonzeroUniform (y (omittedLabel pOut)) *
            response pOut pIn h (fun i : Retained pOut => y i.val)) ∧
      ((∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
        (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) =
        ∑ y, response pOut pIn h y ^ 2) := by
  obtain ⟨h, hzero, hsum, hsource, henergy⟩ := word_source_representation pIn f
  exact ⟨h, hzero, hsum, hsource, henergy,
    selectedStep_action_eq pOut pIn _ h hsource,
    selectedStep_energy_eq pOut pIn _ h hsource⟩

theorem rawFull_response_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) = 0 := by
  funext y
  exact TripleUniformFullResponse.rawFullResponse_zero pOut pIn h y

theorem quadruple_events_zero_kernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (uv : SourceWord pIn)
    (h0 : eventValue pOut pIn 0 uv = 0) (h1 : eventValue pOut pIn 1 uv = 0)
    (h2 : eventValue pOut pIn 2 uv = 0) (h3 : eventValue pOut pIn 3 uv = 0) :
    residualKernel pOut pIn y uv = 0 := by
  have hall : ∀ i : Fin 4, eventValue pOut pIn i uv = 0 := by
    intro i
    fin_cases i <;> assumption
  have hp := (all_event_values_zero_iff pOut pIn uv).mp hall
  exact TripleUniformFullResponse.quadruple_zero_kernel pOut pIn y uv hp.2 hp.1

/-- Four normalized factors have denominator sqrt(q-1)^4 = (q-1)^2. -/
theorem normalizer_eq :
    FourteenResponse.normalizer AES.Word = (ActivityCodeScalar.q - 1) ^ 2 := by
  rw [FourteenResponse.normalizer_eq AES.Word (le_of_lt AES.word_card_gt_one),
    TripleUniformEventGeometry.word_card_real]

/-- Exact fourteen-term response identity, before any energy aggregation. -/
theorem response_eq_fourteen (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    response pOut pIn h = fun y =>
      FourteenResponse.aggregate
        (FourteenResponse.singleResponses (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (eventValue pOut pIn))
        (FourteenResponse.pairResponses (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (eventValue pOut pIn))
        (FourteenResponse.tripleResponses (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (eventValue pOut pIn)) y /
        (ActivityCodeScalar.q - 1) ^ 2 := by
  unfold response
  rw [FourteenResponse.weightedResponse_eq_fourteen _ _ _ (rawFull_response_zero pOut pIn h)
    (quadruple_events_zero_kernel pOut pIn), normalizer_eq]

end AESConcrete.TripleUniformMinorResponse
