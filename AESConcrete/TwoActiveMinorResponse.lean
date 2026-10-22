import AESConcrete.TwoActiveGeometry
import AESConcrete.WeightedResponse
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# Actual signed minor response for a two-active source

The original selected tensor is reduced to its two retained physical outputs.
The same signed source amplitude supplies three nonzero-uniform weights.
Actual MDS zero intersections annihilate the residual product before any norm
bound is applied. No physical energy cap or inventory increment is asserted.
Constructive AES 10/14/16 continuation only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoActiveMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoActiveSource
open AESConcrete.TwoActiveGeometry
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

abbrev Retained (p : SelectedSupport 2 4) := MaskCoordinates p.val.val.1
abbrev Omitted (p : SelectedSupport 2 4) :=
  GeneralMDSGraphSupport.OtherCoordinates p.val.val.1

theorem omitted_card (p : SelectedSupport 2 4) : Fintype.card (Omitted p) = 2 := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, retainedMask_size]

/-- An enumeration of the two omitted labels; their physical values remain
explicit through `omittedLabel` rather than becoming anonymous coordinates. -/
def omittedEquiv (p : SelectedSupport 2 4) : Omitted p ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [omitted_card]; simp)

def omittedLabel (p : SelectedSupport 2 4) (k : Fin 2) : Fin 4 :=
  ((omittedEquiv p).symm k).val

theorem omittedLabel_ne (p : SelectedSupport 2 4) :
    omittedLabel p 0 ≠ omittedLabel p 1 := by
  intro he
  have hs : (omittedEquiv p).symm 0 = (omittedEquiv p).symm 1 := Subtype.ext he
  have hn := (omittedEquiv p).symm.injective hs
  exact (by decide : (0 : Fin 2) ≠ 1) hn

def curve (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (uv : AES.Word × AES.Word) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv (source pIn uv.1 uv.2) i.val

def residualKernel (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (y : Retained pOut → AES.Word) (uv : AES.Word × AES.Word) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn uv i)

def omittedValue (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (k : Fin 2) (uv : AES.Word × AES.Word) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut k)

def response (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (h : AES.Word → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.weightedResponse (fun uv : AES.Word × AES.Word => h uv.1)
    (residualKernel pOut pIn) Prod.snd
    (omittedValue pOut pIn 0) (omittedValue pOut pIn 1)

/-- Exact restriction to the entire two-dimensional source plane. -/
theorem supported_sum (p : SelectedSupport 1 2) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ OnPlane p x → F x = 0) :
    (∑ x, F x) = ∑ uv : AES.Word × AES.Word, F (source p uv.1 uv.2) := by
  calc
    (∑ x, F x) = ∑ x, if OnPlane p x then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : OnPlane p x <;> simp [hx, hF x]
    _ = ∑ x : {x : AES.WordState // OnPlane p x}, F x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := ((sourcePlaneEquiv (V := AES.Word) p).sum_comp
      (fun x => F x.val)).symm

theorem omitted_product (p : SelectedSupport 2 4) (x : AES.WordState) :
    (∏ j : Omitted p, nonzeroUniform (x j.val)) =
      nonzeroUniform (x (omittedLabel p 0)) * nonzeroUniform (x (omittedLabel p 1)) := by
  rw [← (omittedEquiv p).symm.prod_comp (fun j : Omitted p => nonzeroUniform (x j.val))]
  simp only [Fin.prod_univ_two, omittedLabel]

theorem omittedWeight_eq (p : SelectedSupport 2 4) (j : Omitted p) (x : AES.Word) :
    nonzeroWeight (selectedRetained 2 4 p) (selectedZeros 2 4 p) j x = nonzeroUniform x := by
  have hz := RetainedGraphMasks.fullActive_selectedZeros_empty 2 p j.val
  simp only [nonzeroWeight, if_neg hz]

/-- The actual retained minor equals the signed source-plane response,
including all three exclusion weights exactly once. -/
theorem minorResponse_eq (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) = h u * nonzeroUniform v)
    (hoff : ∀ x, ¬ OnPlane pIn x → G x = 0) :
    minorResponse (selectedRetained 2 4 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut))
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
  unfold response WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro uv _
  rw [hsource]
  unfold minorKernel
  have ho : (∏ j : Omitted pOut,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j
        (wordMixAddEquiv (source pIn uv.1 uv.2) j.val)) =
      nonzeroUniform (omittedValue pOut pIn 0 uv) *
      nonzeroUniform (omittedValue pOut pIn 1 uv) := by
    simp_rw [omittedWeight_eq]
    exact omitted_product pOut _
  unfold selectedRetained at ho
  rw [counting_prod_instances (X := Omitted pOut) _ inferInstance, ho]
  unfold residualKernel curve
  rw [counting_prod_instances (X := Retained pOut) _ inferInstance]
  ring

/-- Exact energy equality back to the actual selected physical tensor. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) = h u * nonzeroUniform v)
    (hoff : ∀ x, ¬ OnPlane pIn x → G x = 0) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource hoff]
  exact counting_sum_instances _ _ (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

theorem residualKernel_zero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (y : Retained pOut → AES.Word) : residualKernel pOut pIn y (0, 0) = 0 := by
  have hcard : Fintype.card (Retained pOut) = 2 := by
    rw [maskCoordinates_card, retainedMask_size]
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [curve, source_zero, map_zero, Pi.zero_apply, AES.word_residual_zero_column]

/-- Three actual MDS intersection checks, independent of the amplitude. -/
theorem pairwise_zero_kernel (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2) :
    (∀ y uv, uv.2 = 0 → omittedValue pOut pIn 0 uv = 0 → residualKernel pOut pIn y uv = 0) ∧
    (∀ y uv, uv.2 = 0 → omittedValue pOut pIn 1 uv = 0 → residualKernel pOut pIn y uv = 0) ∧
    (∀ y uv, omittedValue pOut pIn 0 uv = 0 → omittedValue pOut pIn 1 uv = 0 →
      residualKernel pOut pIn y uv = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y uv hv hz
    rw [word_uniform_zero_and_output_zero pIn uv (omittedLabel pOut 0) hv hz]
    exact residualKernel_zero pOut pIn y
  · intro y uv hv hz
    rw [word_uniform_zero_and_output_zero pIn uv (omittedLabel pOut 1) hv hz]
    exact residualKernel_zero pOut pIn y
  · intro y uv hi hj
    rw [word_two_output_zeros_force_zero pIn uv _ _ (omittedLabel_ne pOut) hi hj]
    exact residualKernel_zero pOut pIn y

theorem response_eq_four (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 2)
    (h : AES.Word → ℝ) :
    response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (fun uv : AES.Word × AES.Word => h uv.1)
          (residualKernel pOut pIn) y -
        WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
          (residualKernel pOut pIn) Prod.snd y -
        WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn 0) y -
        WeightedResponse.zeroResponse (fun uv : AES.Word × AES.Word => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn 1) y) /
        WeightedResponse.normalizer AES.Word := by
  obtain ⟨ha, hb, hc⟩ := pairwise_zero_kernel pOut pIn
  exact WeightedResponse.weightedResponse_eq_four _ _ _ _ _ ha hb hc

end AESConcrete.TwoActiveMinorResponse
