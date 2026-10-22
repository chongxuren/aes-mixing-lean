import AESConcrete.ThreeActiveGeometry
import AESConcrete.TripleResponse
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# Actual signed minor response for a three-active source

The selected tensor reduces to its three retained physical outputs. The same
signed joint residual amplitude supplies one source and one omitted-output
nonzero-uniform weight. Their intersection remains in the exact response.
No physical cap or inventory increment is asserted before energy aggregation.
Constructive AES 10/14/16 continuation only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeActiveSource
open AESConcrete.ThreeActiveGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

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

abbrev Retained (p : SelectedSupport 3 4) := MaskCoordinates p.val.val.1
abbrev Omitted (p : SelectedSupport 3 4) :=
  GeneralMDSGraphSupport.OtherCoordinates p.val.val.1

def omittedOther (p : SelectedSupport 3 4) : Omitted p :=
  ⟨omittedLabel p, omittedLabel_not_retained p⟩

theorem omittedOther_unique (p : SelectedSupport 3 4) (i : Omitted p) :
    i = omittedOther p := by
  apply Subtype.ext
  let j : OmittedPositions p := ⟨i.val, by
    change AES.maskBit (maskComplement p.val.val.1) i.val = true
    rw [maskComplement_bit]
    cases hb : AES.maskBit p.val.val.1 i.val <;> simp_all [i.property]⟩
  exact congrArg (fun k : OmittedPositions p => k.val) (omittedPosition_unique p j)

abbrev SourceDomain (p : SelectedSupport 2 3) :=
  (ResidualPositions p → AES.Word) × AES.Word

def curve (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (uv : SourceDomain pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv (source pIn uv.1 uv.2) i.val

def residualKernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (y : Retained pOut → AES.Word) (uv : SourceDomain pIn) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn uv i)

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (uv : SourceDomain pIn) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut)

def response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  TripleResponse.weightedResponse (fun uv : SourceDomain pIn => h uv.1)
    (residualKernel pOut pIn) Prod.snd
    (omittedValue pOut pIn)

/-- Exact restriction to the entire three-dimensional source. -/
theorem supported_sum (p : SelectedSupport 2 3) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ OnSource p x → F x = 0) :
    (∑ x, F x) = ∑ uv : SourceDomain p, F (source p uv.1 uv.2) := by
  calc
    (∑ x, F x) = ∑ x, if OnSource p x then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : OnSource p x <;> simp [hx, hF x]
    _ = ∑ x : {x : AES.WordState // OnSource p x}, F x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := ((sourceEquiv (V := AES.Word) p).sum_comp
      (fun x => F x.val)).symm

theorem omitted_product (p : SelectedSupport 3 4) (x : AES.WordState) :
    (∏ j : Omitted p, nonzeroUniform (x j.val)) = nonzeroUniform (x (omittedLabel p)) := by
  rw [Finset.prod_eq_single (omittedOther p)]
  · rfl
  · intro i _ hi
    exact (hi (omittedOther_unique p i)).elim
  · simp

theorem omittedWeight_eq (p : SelectedSupport 3 4) (j : Omitted p) (x : AES.Word) :
    nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p) j x = nonzeroUniform x := by
  have hz := RetainedGraphMasks.fullActive_selectedZeros_empty 3 p j.val
  simp only [nonzeroWeight, if_neg hz]

/-- The actual retained minor equals the signed source-plane response,
including both exclusion weights exactly once. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) = h u * nonzeroUniform v)
    (hoff : ∀ x, ¬ OnSource pIn x → G x = 0) :
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
  rw [supported_sum pIn _ (by
    intro x hx
    rw [hoff x hx, mul_zero])]
  unfold response TripleResponse.weightedResponse
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
  unfold residualKernel curve
  rw [counting_prod_instances (X := Retained pOut) _ inferInstance]
  ring

/-- Exact energy equality back to the actual selected physical tensor. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (G : AES.WordState → ℝ) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (hsource : ∀ u v, G (source pIn u v) = h u * nonzeroUniform v)
    (hoff : ∀ x, ¬ OnSource pIn x → G x = 0) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource hoff]
  exact counting_sum_instances _ _ (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

/-- The intersection line is retained in the exact signed decomposition. -/
theorem response_eq_four (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) y -
        WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) Prod.snd y -
        WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) Prod.snd (omittedValue pOut pIn) y) /
        TripleResponse.normalizer AES.Word :=
  TripleResponse.weightedResponse_eq_four _ _ _ _

end AESConcrete.ThreeActiveMinorResponse
