import AESConcrete.DoubleUniformGeometry
import AESConcrete.SevenResponse
import AESConcrete.ActivityMinorInput
import AESConcrete.RetainedGraphMasks

/-!
# Actual three-exclusion response for the (1,3) source and (3,4) output

Both original uniform input labels are retained in the physical source.
Together with the one omitted output, they supply exactly three normalized
exclusion weights. Only their triple intersection kills the residual kernel;
all three pair intersections remain in the seven-term signed identity.
The same unrestricted signed residual amplitude is used in every term.

Candidate only. Constructive mathematics only; no attacks. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct reference
pairs and the fixed 10/14/16 target remain unchanged. No cap or inventory entry
is asserted by this response identity.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformMinorResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
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

/-- A fixed indexing choice for the two original labels, independent of h. -/
def uniformIndexEquiv (p : SelectedSupport 1 3) : SourceUniformPositions p ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (p : SelectedSupport 1 3) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 0

def uniformSecond (p : SelectedSupport 1 3) : SourceUniformPositions p :=
  (uniformIndexEquiv p).symm 1

theorem uniformFirst_ne_second (p : SelectedSupport 1 3) : uniformFirst p ≠ uniformSecond p := by
  intro he
  have hf : (0 : Fin 2) = 1 := by
    simpa only [uniformFirst, uniformSecond, Equiv.apply_symm_apply] using
      congrArg (uniformIndexEquiv p) he
  exact (by decide : (0 : Fin 2) ≠ 1) hf

theorem uniform_product (p : SelectedSupport 1 3) (v : SourceUniformPositions p → AES.Word) :
    (∏ j : SourceUniformPositions p, nonzeroUniform (v j)) =
      nonzeroUniform (v (uniformFirst p)) * nonzeroUniform (v (uniformSecond p)) := by
  have hp := (uniformIndexEquiv p).symm.prod_comp
    (fun j : SourceUniformPositions p => nonzeroUniform (v j))
  simpa only [Fin.prod_univ_two, uniformFirst, uniformSecond] using hp.symm

theorem uniform_tuple_eq_zero {V : Type*} [Zero V]
    (p : SelectedSupport 1 3) (v : SourceUniformPositions p → V)
    (hfirst : v (uniformFirst p) = 0) (hsecond : v (uniformSecond p) = 0) : v = 0 := by
  funext j
  have hjlt := (uniformIndexEquiv p j).isLt
  have hjval : (uniformIndexEquiv p j).val = 0 ∨ (uniformIndexEquiv p j).val = 1 := by omega
  rcases hjval with hjval | hjval
  · have hj : j = uniformFirst p := by
      apply (uniformIndexEquiv p).injective
      change uniformIndexEquiv p j = uniformIndexEquiv p ((uniformIndexEquiv p).symm 0)
      rw [Equiv.apply_symm_apply]
      exact Fin.ext hjval
    simpa only [hj, Pi.zero_apply] using hfirst
  · have hj : j = uniformSecond p := by
      apply (uniformIndexEquiv p).injective
      change uniformIndexEquiv p j = uniformIndexEquiv p ((uniformIndexEquiv p).symm 1)
      rw [Equiv.apply_symm_apply]
      exact Fin.ext hjval
    simpa only [hj, Pi.zero_apply] using hsecond

abbrev Retained (p : SelectedSupport 3 4) := MaskCoordinates p.val.val.1
abbrev Omitted (p : SelectedSupport 3 4) :=
  GeneralMDSGraphSupport.OtherCoordinates p.val.val.1

def omittedOther (p : SelectedSupport 3 4) : Omitted p :=
  ⟨omittedLabel p, omittedLabel_not_retained p⟩

theorem omittedOther_unique (p : SelectedSupport 3 4) (i : Omitted p) : i = omittedOther p := by
  apply Subtype.ext
  let j : OmittedPositions p := ⟨i.val, by
    change AES.maskBit (maskComplement p.val.val.1) i.val = true
    rw [maskComplement_bit]
    cases hb : AES.maskBit p.val.val.1 i.val <;> simp_all [i.property]⟩
  exact congrArg (fun k : OmittedPositions p => k.val) (omittedPosition_unique p j)

abbrev SourceDomain (p : SelectedSupport 1 3) := AES.Word × (SourceUniformPositions p → AES.Word)

def curve (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (uv : SourceDomain pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv (source pIn uv.1 uv.2) i.val

def residualKernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (uv : SourceDomain pIn) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn uv i)

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (uv : SourceDomain pIn) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut)

def response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (h : AES.Word → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.weightedResponse (fun uv : SourceDomain pIn => h uv.1)
    (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
    (fun uv => uv.2 (uniformSecond pIn)) (omittedValue pOut pIn)

/-- Restriction to all three actual active input coordinates, including zero. -/
theorem supported_sum (p : SelectedSupport 1 3) (F : AES.WordState → ℝ)
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
    _ = _ := ((sourceEquiv (V := AES.Word) p).sum_comp (fun x => F x.val)).symm

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

/-- Exactly two source weights and one omitted-output weight occur once each. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j))
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
  unfold response WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro uv _
  rw [hsource, uniform_product]
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

/-- Counting energy back to the actual selected physical tensor. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j))
    (hoff : ∀ x, ¬ OnSource pIn x → G x = 0) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G h hsource hoff]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

/-- The arbitrary signed amplitude is extracted from the actual support component. -/
theorem selected_component_response (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      (∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2) = ∑ u, h u ^ 2 ∧
      (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
        (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) =
        ∑ y, response pOut pIn h y ^ 2 := by
  obtain ⟨h, hsource, henergy, hoff⟩ := word_source_representation pIn f
  exact ⟨h, henergy, selectedStep_energy_eq pOut pIn _ h hsource hoff⟩

theorem residualKernel_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) : residualKernel pOut pIn y (0, 0) = 0 := by
  have hcard : Fintype.card (Retained pOut) = 3 := by
    rw [maskCoordinates_card, retainedMask_size]
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [curve, source_zero, map_zero, Pi.zero_apply, AES.word_residual_zero_column]

/-- Only the triple intersection is killed. Pair intersections remain untouched. -/
theorem triple_zero_kernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (uv : SourceDomain pIn)
    (hfirst : uv.2 (uniformFirst pIn) = 0) (hsecond : uv.2 (uniformSecond pIn) = 0)
    (hz : omittedValue pOut pIn uv = 0) : residualKernel pOut pIn y uv = 0 := by
  have hv : uv.2 = 0 := uniform_tuple_eq_zero pIn uv.2 hfirst hsecond
  have hz' : wordMixAddEquiv (Pi.single (residualLabel pIn) uv.1) (omittedLabel pOut) = 0 := by
    simpa only [omittedValue, hv, source_residual_axis] using hz
  have hu : uv.1 = 0 := by
    have hcoerce (x : AES.WordState) :
        wordMixAddEquiv.toAddMonoidHom x = wordMixAddEquiv x := rfl
    apply (TwoActiveGeometry.singletonCoordinateEquiv wordMixAddEquiv.toAddMonoidHom
      WordCrossZero.wordMixAddEquiv_zeroMDS (residualLabel pIn) (omittedLabel pOut)).injective
    rw [TwoActiveGeometry.singletonCoordinateEquiv_zero]
    simpa only [TwoActiveGeometry.singletonCoordinateEquiv_apply, hcoerce] using hz'
  have huv : uv = (0, 0) := Prod.ext hu hv
  rw [huv]
  exact residualKernel_zero pOut pIn y

/-- Full minus three planes plus all three lines, before any norm estimate. -/
theorem response_eq_seven (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (h : AES.Word → ℝ) :
    response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) y -
        WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn)) y -
        WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn)) y -
        WeightedResponse.zeroResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
          (fun uv => uv.2 (uniformSecond pIn)) y +
        TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformFirst pIn))
          (omittedValue pOut pIn) y +
        TripleResponse.intersectionResponse (fun uv : SourceDomain pIn => h uv.1)
          (residualKernel pOut pIn) (fun uv => uv.2 (uniformSecond pIn))
          (omittedValue pOut pIn) y) / WeightedResponse.normalizer AES.Word :=
  SevenResponse.weightedResponse_eq_seven _ _ _ _ _ (triple_zero_kernel pOut pIn)

end AESConcrete.DoubleUniformMinorResponse
