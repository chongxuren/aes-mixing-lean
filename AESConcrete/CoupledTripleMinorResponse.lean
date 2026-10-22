import AESConcrete.CoupledTripleSource
import AESConcrete.CoupledTripleFullEnergy
import AESConcrete.TripleResponse
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# Actual selected minor for a joint residual triple and one uniform input

The support indices are `(12,12)`.

The full four-word source is a residual triple plus its ORIGINAL scalar
uniform complement. The input uniform factor and omitted-output factor occur
exactly once each. The retained image is never substituted for the full source
by an injectivity assumption. The raw full response and the intersection both
survive in the four-term identity. The same arbitrary signed JOINT h occurs in
every term; no factorization or vanishing-at-zero hypothesis is imposed.

This component supplies exact source/minor/tensor and energy identities only.
The four response estimates, scalar envelope, physical factor16, certificate
comparison and operator integration remain separate. Constructive fixed
independent-uniform-retained-key AES10/14/16, whitening, omitted final
MixColumns and ordered-distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber (ResidualPositions)
open AESConcrete.CoupledTripleSource
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
  Subtype.ext (CoupledTripleFiber.nonretained_eq_omitted pOut j.val j.property)

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
theorem full_source_sum (pIn : SelectedSupport 3 4) (F : AES.WordState → ℝ) :
    (∑ x, F x) = ∑ uv : SourceWord pIn, F (source pIn uv.1 uv.2) :=
  ((sourceWordEquiv pIn).sum_comp F).symm

def retainedMap (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (uv : SourceWord pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv (source pIn uv.1 uv.2) i.val

def residualKernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (y : Retained pOut → AES.Word) (uv : SourceWord pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedMap pOut pIn uv i)

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (uv : SourceWord pIn) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut)

/-- The original scalar input weight and the omitted output weight. -/
def response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  TripleResponse.weightedResponse (fun uv : SourceWord pIn => h uv.1)
    (residualKernel pOut pIn) (fun uv => uv.2) (omittedValue pOut pIn)

/-- Each physical uniform factor occurs once, with the same joint h. -/
theorem response_eq_source_weights (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    response pOut pIn h y = ∑ uv : SourceWord pIn,
      (h uv.1 * nonzeroUniform uv.2) *
        nonzeroUniform (omittedValue pOut pIn uv) * residualKernel pOut pIn y uv := rfl

/-- Pointwise retained-minor identity, using the full four-word source sum. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * nonzeroUniform v) :
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
theorem selectedStep_action_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * nonzeroUniform v)
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
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * nonzeroUniform v) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

/-- The actual extracted amplitude keeps its source constraints and exact energy. -/
theorem selected_component_response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (f : AES.WordState → ℝ) :
    ∃ h : (ResidualPositions pIn → AES.Word) → ℝ,
      markedResidual pIn.val.val.1 h = h ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) pIn.val f (source pIn u v) =
        h u * nonzeroUniform v) ∧
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
theorem rawFull_response_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y = CoupledTripleFullEnergy.rawFullResponse pIn pOut h y := by
  have he := (sourceWordEquiv pIn).sum_comp (fun s : AES.WordState =>
    h (CoupledTripleFiber.residualHom pIn s) *
      ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv s i.val))
  change (∑ uv : SourceWord pIn,
    h (CoupledTripleFiber.residualHom pIn (source pIn uv.1 uv.2)) *
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i)
        (wordMixAddEquiv (source pIn uv.1 uv.2) i.val)) = _ at he
  simp_rw [residualHom_source] at he
  exact he

/-- Two actual exclusions yield four terms, with neither endpoint discarded. -/
theorem response_eq_four (pOut pIn : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) y -
        WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2) y -
        WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2)
          (omittedValue pOut pIn) y) / TripleResponse.normalizer AES.Word :=
  TripleResponse.weightedResponse_eq_four _ _ _ _

end AESConcrete.CoupledTripleMinorResponse
