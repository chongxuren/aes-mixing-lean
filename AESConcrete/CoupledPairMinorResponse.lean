import AESConcrete.CoupledPairSource
import AESConcrete.CoupledPairFullEnergy
import AESConcrete.EightResponse
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# Actual selected-minor response for a joint residual pair

The full four-word source is reindexed by its actual equivalence. Both
original uniform-input factors and the omitted-output factor occur once each.
The retained triple is not silently used as an injective parameterization of
the unrestricted source.

Pointwise minor and selected-tensor identities precede exact counting-energy
transport. All eight signed responses, including full and triple endpoints,
remain in the response identity. This source asserts no event-energy bound,
physical cap or inventory addition. Constructive fixed AES10/14/16 independent
uniform retained keys, whitening, omitted final MixColumns and ordered-
distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairFiber (ResidualPositions)
open AESConcrete.CoupledPairSource
open AESConcrete.ThreeActiveGeometry (omittedLabel omittedLabel_not_retained)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction
  (minorResponse minorKernel nonzeroWeight coordinateKernel_rank_one_minor)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)

abbrev Retained (pOut : SelectedSupport 3 4) := MaskCoordinates pOut.val.val.1

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
  Subtype.ext (CoupledPairFiber.nonretained_eq_omitted pOut j.val j.property)

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
theorem full_source_sum (pIn : SelectedSupport 2 4) (F : AES.WordState → ℝ) :
    (∑ x, F x) = ∑ uv : SourceWord pIn, F (source pIn uv.1 uv.2) :=
  ((sourceWordEquiv pIn).sum_comp F).symm

/-- A support-dependent choice of order for the two original uniform labels. -/
def uniformIndexEquiv (p : SelectedSupport 2 4) : SourceUniformPositions p ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (p : SelectedSupport 2 4) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 0

def uniformSecond (p : SelectedSupport 2 4) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 1

theorem uniformFirst_ne_second (p : SelectedSupport 2 4) : uniformFirst p ≠ uniformSecond p := by
  intro he
  have hf : (0 : Fin 2) = 1 := by
    simpa only [uniformFirst, uniformSecond, Equiv.apply_symm_apply] using
      congrArg (uniformIndexEquiv p) he
  exact (by decide : (0 : Fin 2) ≠ 1) hf

theorem uniform_product (pIn : SelectedSupport 2 4)
    (v : SourceUniformPositions pIn → AES.Word) :
    (∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) =
      nonzeroUniform (v (uniformFirst pIn)) * nonzeroUniform (v (uniformSecond pIn)) := by
  have hp := (uniformIndexEquiv pIn).symm.prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (v j))
  simpa only [Fin.prod_univ_two, uniformFirst, uniformSecond] using hp.symm

def retainedMap (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv (source pIn uv.1 uv.2) i.val

def residualKernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) (uv : SourceWord pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedMap pOut pIn uv i)

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut)

/-- The original two input weights and the omitted output weight. -/
def response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.weightedResponse (fun uv : SourceWord pIn => h uv.1)
    (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
    (fun uv => uv.2 (uniformSecond pIn)) (omittedValue pOut pIn)

/-- Each physical uniform factor occurs once, with the same joint h. -/
theorem response_eq_source_weights (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    response pOut pIn h y = ∑ uv : SourceWord pIn,
      (h uv.1 * ∏ j : SourceUniformPositions pIn, nonzeroUniform (uv.2 j)) *
        nonzeroUniform (omittedValue pOut pIn uv) * residualKernel pOut pIn y uv := by
  unfold response WeightedResponse.weightedResponse
  simp_rw [uniform_product]
  apply Finset.sum_congr rfl
  intro uv _
  ring

/-- Pointwise retained-minor identity, using the full four-word source sum. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
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
  unfold residualKernel retainedMap
  rw [counting_prod_instances (X := Retained pOut) _ inferInstance]
  ring

/-- The full output is the retained response times its one unit output leg. -/
theorem selectedStep_action_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
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
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

/-- The actual extracted amplitude keeps its source constraints and exact energy. -/
theorem selected_component_response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (f : AES.WordState → ℝ) :
    ∃ h : (ResidualPositions pIn → AES.Word) → ℝ,
      markedResidual pIn.val.val.1 h = h ∧
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
  obtain ⟨h, hh, hsource, henergy⟩ := word_source_representation pIn f
  exact ⟨h, hh, hsource, henergy,
    selectedStep_action_eq pOut pIn _ h hsource,
    selectedStep_energy_eq pOut pIn _ h hsource⟩

/-- Exact full response transport keeps the joint residual amplitude. -/
theorem rawFull_response_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y = CoupledPairFullEnergy.rawFullResponse pIn pOut h y := by
  have he := (sourceWordEquiv pIn).sum_comp (fun s : AES.WordState =>
    h (CoupledPairFiber.residualHom pIn s) *
      ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv s i.val))
  change (∑ uv : SourceWord pIn,
    h (CoupledPairFiber.residualHom pIn (source pIn uv.1 uv.2)) *
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i)
        (wordMixAddEquiv (source pIn uv.1 uv.2) i.val)) = _ at he
  simp_rw [residualHom_source] at he
  exact he

/-- Complete inclusion-exclusion; neither endpoint is discarded. -/
theorem response_eq_eight (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) y -
        WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn)) y -
        WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn)) y -
        WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
          (fun uv => uv.2 (uniformSecond pIn)) y +
        TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
          (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn))
          (omittedValue pOut pIn) y -
        EightResponse.tripleIntersectionResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
          (fun uv => uv.2 (uniformSecond pIn)) (omittedValue pOut pIn) y) /
        WeightedResponse.normalizer AES.Word :=
  EightResponse.weightedResponse_eq_eight _ _ _ _ _

end AESConcrete.CoupledPairMinorResponse
