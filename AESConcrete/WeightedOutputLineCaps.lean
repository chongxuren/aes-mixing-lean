import AESConcrete.WeightedOutputLineGeometry
import AESConcrete.IndexedTripleEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityMinorInput
import AESConcrete.MultiUniformExpansion
import AESConcrete.UniformGraphCaps
import AESConcrete.ActivityCodeScalar

/-!
# Exact omitted output uniform and signed weighted-line energy

Lemmas for (9,5) and (9,8). Actual output type(2,3) has one omitted zero-unit
factor and one omitted normalized nonzeroUniform factor. The latter stays
inside the SAME exact amplitude on the shortened code, alongside the original
arbitrary signed joint h and its(2-e) actual input uniforms. The exact
selectedWordTensor output unit-energy embedding is a separate identity, not a
second normalization.

Input residual-tuple injection is independent of output parametrization. It
supplies subenergy after pointwise uniform bounds; no physical-coordinate
independence, residual factorization, h positivity or h(0)=0 is assumed.
Physical multiplicities and unchanged L comparisons belong in StepCaps.

Constructive fixed AES10/14/16 independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedOutputLineCaps
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedOutputLineGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.NonzeroUniformGraphCap (zeroUnit nonzeroUniform)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion (multiUniform normalizedLeg InactivePositions)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

variable {e : Fin 5}

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

/-- Only actual input inactivity is required of the arbitrary signed source. -/
def InputSupported (pIn : SelectedSupport e 2) (G : AES.WordState → ℝ) : Prop :=
  ∀ x, G x ≠ 0 → ∀ i, maskBit pIn.val.val.2 i = true → x i = 0

theorem component_supported (pIn : SelectedSupport e 2) (f : AES.WordState → ℝ) :
    InputSupported pIn (supportIndexComponent (0 : AES.Word) pIn.val f) := by
  intro x hx i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero pIn.val i hi f x hx

/-- The actual omitted nonzero-uniform output labels. -/
abbrev OutputUniformPositions (pOut : SelectedSupport 2 3) :=
  MultiUniformExpansion.UniformPositions pOut.val.val.2 pOut.val.val.1

theorem outputUniformPositions_card (pOut : SelectedSupport 2 3) :
    Fintype.card (OutputUniformPositions pOut) = 1 := by
  calc
    Fintype.card (OutputUniformPositions pOut) =
        (3 : Fin 5).val - (2 : Fin 5).val := by
      simpa only [OutputUniformPositions, ← Nat.card_eq_fintype_card] using
        UniformGraphCaps.selected_uniformPositions_card 2 3 pOut
    _ = 1 := by decide

/-- Keep the output uniform at its original physical label. -/
def outputUniformWeight (pOut : SelectedSupport 2 3) (x : AES.WordState) : ℝ :=
  ∏ i : OutputUniformPositions pOut, nonzeroUniform (x i.val.val)

/-- Zero-unit omission and output uniform omission are distinct factors.
Only the former restricts the graph; no output denominator is inserted. -/
theorem omittedWeight_product (pOut : SelectedSupport 2 3) (x : AES.WordState) :
    (∏ j : OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut) j (x j.val)) =
      (if ∀ i, maskBit pOut.val.val.2 i = true → x i = 0 then 1 else 0) *
        outputUniformWeight pOut x := by
  rw [counting_prod_instances (X := OtherCoordinates pOut.val.val.1) _ inferInstance]
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : OtherCoordinates pOut.val.val.1 => maskBit pOut.val.val.2 i.val = true)]
  have hI (i : InactivePositions pOut.val.val.2 pOut.val.val.1) :
      nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut) i.val
        (x i.val.val) = zeroUnit (x i.val.val) := by
    simp [nonzeroWeight, selectedZeros, i.property]
  have hA (i : OutputUniformPositions pOut) :
      nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut) i.val
        (x i.val.val) = nonzeroUniform (x i.val.val) := by
    simp [nonzeroWeight, selectedZeros, i.property]
  simp_rw [hI, hA]
  have hz : (∏ i : InactivePositions pOut.val.val.2 pOut.val.val.1,
      zeroUnit (x i.val.val)) =
      if ∀ i, maskBit pOut.val.val.2 i = true → x i = 0 then 1 else 0 := by
    by_cases hx : ∀ i, maskBit pOut.val.val.2 i = true → x i = 0
    · rw [if_pos hx]
      apply Finset.prod_eq_one
      intro i _
      simp [zeroUnit, supportConstant, identityKernel, hx i.val.val i.property]
    · rw [if_neg hx]
      obtain ⟨i, hi, hxi⟩ : ∃ i, maskBit pOut.val.val.2 i = true ∧ x i ≠ 0 := by
        simpa using hx
      have hE := output_inactive_not_retained pOut i hi
      apply Finset.prod_eq_zero
        (Finset.mem_univ (⟨⟨i, hE⟩, hi⟩ : InactivePositions pOut.val.val.2 pOut.val.val.1))
      simp [zeroUnit, supportConstant, identityKernel, hxi]
  rw [hz]
  rfl

/-- Exact restriction to the physical three-zero line; no normalization is inserted. -/
theorem line_supported_sum (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 x → F x = 0) :
    (∑ x, F x) = ∑ c : LineCode pOut pIn, F c.val := by
  calc
    (∑ x, F x) = ∑ x, if graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · exact hF x hx
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _
        (by intro x; simp [ShortenedWeightedGeometry.shortenedSubgroup]) _

/-- Unnormalized two-retained-output response of the actual physical line. -/
def response (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2) (G : AES.WordState → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => G c.val * outputUniformWeight pOut (wordMixAddEquiv c.val))

/-- Exact original minor transport, before applying any analytic bound.
The input and output zero conditions are retained in the source subtype. -/
theorem minorResponse_eq (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    minorResponse (selectedRetained 2 3 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) = response pOut pIn G := by
  unfold selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut) j
          (wordMixAddEquiv x j.val)) =
        (if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
          outputUniformWeight pOut (wordMixAddEquiv x) :=
    omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x =>
    (∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)) *
      ((if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
        outputUniformWeight pOut (wordMixAddEquiv x)) * G x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      by_cases hg : G x = 0
      · simp only [F, hg, mul_zero]
      · have hz : ∀ i, maskBit pIn.val.val.2 i = true → x i = 0 := hG x hg
        have ho : ¬ ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 :=
          fun ho => hx ⟨ho, hz⟩
        simp only [F, if_neg ho, mul_zero, zero_mul]
    rw [line_supported_sum pOut pIn F hF]
    unfold response IndexedTripleEnergy.response
    apply Finset.sum_congr rfl
    intro c _
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    dsimp only [F]
    rw [if_pos ho, one_mul]
    unfold curve
    ring

/-- The unit omitted output vector preserves exact counting energy. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut) G y ^ 2) =
      ∑ y, response pOut pIn G y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G hG]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn G y ^ 2)

/-- One free operator label and one dependent column, on the same signed code.
The generic theorem has an arbitrary retained index type despite its name. -/
theorem code_response_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (mu : LineCode pOut pIn → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (curve pOut pIn) mu y ^ 2) ≤ (rho ^ 2 * kappa) * ∑ c, mu c ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤
        rho ^ 2 * ∑ x, g x ^ 2 := by
    intro g
    simpa only [rho] using SharpDampedWordNorm.word_superbox_residual_energy g
  have hc : ∀ v : AES.Word,
      (∑ y, residualMatrix AES.wordSuperboxKernel 0 y v ^ 2) ≤ kappa := by
    intro v
    simpa only [kappa] using (AllColumnBound.actual_word_residual_column_energy_lt v).le
  have he := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : Retained pOut => i = s) (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) mu (retainedFreeEquiv pOut pIn s)
    (retainedFreeEquiv_apply pOut pIn s) rho kappa kappa_nonneg hT hc
  simpa only [Finset.prod_const, Finset.card_univ,
    IndexedGraphEnergy.FreeCoordinates, Fintype.card_subtype_eq,
    dependentCoordinates_card pOut s, pow_one] using he

/-- Original physical uniform labels, with neither ordering nor independence. -/
abbrev SourceUniformPositions (pIn : SelectedSupport e 2) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

theorem sourceUniformPositions_card (pIn : SelectedSupport e 2) :
    Fintype.card (SourceUniformPositions pIn) = 2 - e.val := by
  have htwo : (2 : Fin 5).val = 2 := rfl
  simpa only [SourceUniformPositions, ← Nat.card_eq_fintype_card, htwo] using
    UniformGraphCaps.selected_uniformPositions_card e 2 pIn

/-- The prescribed normalized source, with one arbitrary signed joint residual. -/
def normalizedSource (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  multiUniform pIn.val.val.2 pIn.val.val.1 h

/-- Only the actual input uniform legs occur in this weight. -/
def uniformWeight (pIn : SelectedSupport e 2) (x : AES.WordState) : ℝ :=
  ∏ i : SourceUniformPositions pIn, nonzeroUniform (x i.val.val)

/-- Public definitions give the exact source split, including its input zero leg.
This is a local derivation; the predecessor's private splitting lemma is unused. -/
theorem normalizedSource_eq (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    normalizedSource pIn h x = h (fun i => x i.val) *
      (∏ i : InactivePositions pIn.val.val.2 pIn.val.val.1,
        zeroUnit (x i.val.val)) * uniformWeight pIn x := by
  unfold normalizedSource multiUniform coordinateEmbedding uniformWeight
  rw [counting_prod_instances (X := OtherCoordinates pIn.val.val.1) _ inferInstance]
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : OtherCoordinates pIn.val.val.1 => maskBit pIn.val.val.2 i.val = true)]
  have hI (i : InactivePositions pIn.val.val.2 pIn.val.val.1) :
      normalizedLeg (maskBit pIn.val.val.2 i.val.val) (x i.val.val) =
        zeroUnit (x i.val.val) := by
    simp [normalizedLeg, i.property]
  have hA (i : SourceUniformPositions pIn) :
      normalizedLeg (maskBit pIn.val.val.2 i.val.val) (x i.val.val) =
        nonzeroUniform (x i.val.val) := by
    simp [normalizedLeg, i.property]
  simp_rw [hI, hA]
  ring

/-- Inactive input support follows for every h, without a residual fixed point. -/
theorem normalizedSource_supported (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) : InputSupported pIn (normalizedSource pIn h) := by
  intro x hx i hi
  by_contra hxi
  have hE : maskBit pIn.val.val.1 i ≠ true := pIn.val.property.1 i hi
  have hp : (∏ j : InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (x j.val.val)) = 0 := by
    apply Finset.prod_eq_zero
      (Finset.mem_univ (⟨⟨i, hE⟩, hi⟩ :
        InactivePositions pIn.val.val.2 pIn.val.val.1))
    simp [zeroUnit, supportConstant, identityKernel, hxi]
  apply hx
  rw [normalizedSource_eq, hp]
  ring

/-- The SAME normalized source restricted to the line keeps its uniform weights. -/
theorem normalizedSource_on_line (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) (c : LineCode pOut pIn) :
    normalizedSource pIn h c.val =
      h (residualTuple pOut pIn c) * uniformWeight pIn c.val := by
  rw [normalizedSource_eq]
  have hp : (∏ i : InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (c.val i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hz := c.property.2 i.val.val i.property
    simp [zeroUnit, supportConstant, identityKernel, hz]
  rw [hp, mul_one]
  rfl

theorem normalizedSource_energy (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 := by
  have ht := MultiUniformExpansion.multiUniform_energy AES.word_card_gt_one
    pIn.val.val.2 pIn.val.val.1 h
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at ht
  exact ht

/-- The squared nonzero-uniform value is bounded pointwise, not in expectation. -/
theorem nonzeroUniform_sq_le (v : AES.Word) : nonzeroUniform v ^ 2 ≤ 1 / (q - 1) := by
  have hcard : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  have hq : 0 ≤ (Fintype.card AES.Word : ℝ) - 1 := by
    rw [hcard]
    exact le_of_lt q_sub_one_pos
  unfold nonzeroUniform
  rw [div_pow, Real.sq_sqrt hq, hcard]
  have hc : supportConstant false v ^ 2 ≤ (1 : ℝ) := by
    by_cases hv : v = 0 <;> simp [supportConstant, identityKernel, hv]
  exact div_le_div_of_nonneg_right hc (le_of_lt q_sub_one_pos)

abbrev uniformSquaredFactor (e : Fin 5) : ℝ := 1 / (q - 1) ^ (2 - e.val)

theorem uniformSquaredFactor_nonneg (e : Fin 5) : 0 ≤ uniformSquaredFactor e :=
  one_div_nonneg.mpr (pow_nonneg (le_of_lt q_sub_one_pos) _)

/-- Bound each actual physical factor before multiplying; coordinates may correlate. -/
theorem uniformWeight_sq_le (pIn : SelectedSupport e 2) (x : AES.WordState) :
    uniformWeight pIn x ^ 2 ≤ uniformSquaredFactor e := by
  unfold uniformWeight
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _i : SourceUniformPositions pIn, (1 / (q - 1) : ℝ) :=
      Finset.prod_le_prod (fun i _ => sq_nonneg (nonzeroUniform (x i.val.val)))
        (fun i _ => nonzeroUniform_sq_le (x i.val.val))
    _ = (1 / (q - 1) : ℝ) ^ (2 - e.val) := by
      simp only [Finset.prod_const, Finset.card_univ, sourceUniformPositions_card]
    _ = uniformSquaredFactor e := by
      simp only [uniformSquaredFactor, div_pow, one_pow]

def weightedAmplitude (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) (c : LineCode pOut pIn) : ℝ :=
  (h (residualTuple pOut pIn c) * uniformWeight pIn c.val) *
    outputUniformWeight pOut (wordMixAddEquiv c.val)

/-- The one actual omitted output uniform is bounded at its real MixColumns value. -/
theorem outputUniformWeight_sq_le (pOut : SelectedSupport 2 3) (x : AES.WordState) :
    outputUniformWeight pOut x ^ 2 ≤ 1 / (q - 1) := by
  unfold outputUniformWeight
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _i : OutputUniformPositions pOut, (1 / (q - 1) : ℝ) :=
      Finset.prod_le_prod (fun i _ => sq_nonneg (nonzeroUniform (x i.val.val)))
        (fun i _ => nonzeroUniform_sq_le (x i.val.val))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, outputUniformPositions_card, pow_one]

abbrev weightedSquaredFactor (e : Fin 5) : ℝ := 1 / (q - 1) ^ (3 - e.val)

theorem weightedSquaredFactor_nonneg (e : Fin 5) : 0 ≤ weightedSquaredFactor e :=
  one_div_nonneg.mpr (pow_nonneg q_sub_one_pos.le _)

/-- Actual input uniforms and the actual omitted output uniform are bounded
pointwise before the separately proved residual INPUT injection is used. -/
theorem weightedAmplitude_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (he : e = 1 ∨ e = 2) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤
      weightedSquaredFactor e * ∑ u, h u ^ 2 := by
  have hpos : 1 ≤ e.val := by rcases he with rfl | rfl <;> decide
  have hf : uniformSquaredFactor e * (1 / (q - 1)) = weightedSquaredFactor e := by
    rcases he with rfl | rfl <;>
      norm_num [uniformSquaredFactor, weightedSquaredFactor] <;>
      field_simp [ne_of_gt q_sub_one_pos] <;> ring
  have hw (c : LineCode pOut pIn) :
      uniformWeight pIn c.val ^ 2 * outputUniformWeight pOut (wordMixAddEquiv c.val) ^ 2 ≤
        weightedSquaredFactor e := by
    rw [← hf]
    exact mul_le_mul (uniformWeight_sq_le pIn c.val)
      (outputUniformWeight_sq_le pOut (wordMixAddEquiv c.val))
      (sq_nonneg _) (uniformSquaredFactor_nonneg e)
  calc
    _ = ∑ c : LineCode pOut pIn, h (residualTuple pOut pIn c) ^ 2 *
        (uniformWeight pIn c.val ^ 2 * outputUniformWeight pOut (wordMixAddEquiv c.val) ^ 2) := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [weightedAmplitude, mul_pow]
      ring
    _ ≤ ∑ c : LineCode pOut pIn, h (residualTuple pOut pIn c) ^ 2 * weightedSquaredFactor e :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hw c) (sq_nonneg _))
    _ = weightedSquaredFactor e *
        ∑ c : LineCode pOut pIn, h (residualTuple pOut pIn c) ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ weightedSquaredFactor e * ∑ u, h u ^ 2 :=
      mul_le_mul_of_nonneg_left (residual_subenergy pOut pIn hpos h)
        (weightedSquaredFactor_nonneg e)

/-- Raw response with the joint residual and its original physical uniform weights. -/
def jointResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (weightedAmplitude pOut pIn h)

theorem response_normalizedSource (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    response pOut pIn (normalizedSource pIn h) = jointResponse pOut pIn h := by
  unfold response jointResponse IndexedTripleEnergy.response
  funext y
  apply Finset.sum_congr rfl
  intro c _
  simp only [normalizedSource_on_line, weightedAmplitude]

abbrev pieceSquaredBound (e : Fin 5) : ℝ := rho ^ 2 * kappa / (q - 1) ^ (3 - e.val)

theorem pieceSquaredBound_nonneg (e : Fin 5) : 0 ≤ pieceSquaredBound e :=
  div_nonneg (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg)
    (pow_nonneg (le_of_lt q_sub_one_pos) _)

/-- One operator leg, one column leg, and the weighted residual-input subenergy. -/
theorem joint_response_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (he : e = 1 ∨ e = 2) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, jointResponse pOut pIn h y ^ 2) ≤
      pieceSquaredBound e * ∑ u, h u ^ 2 := by
  have hb := code_response_energy pOut pIn (weightedAmplitude pOut pIn h)
  have hw := weightedAmplitude_energy pOut pIn he h
  refine hb.trans ?_
  calc
    (rho ^ 2 * kappa) * ∑ c, weightedAmplitude pOut pIn h c ^ 2 ≤
        (rho ^ 2 * kappa) * (weightedSquaredFactor e * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left hw
        (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg)
    _ = pieceSquaredBound e * ∑ u, h u ^ 2 := by
      unfold pieceSquaredBound weightedSquaredFactor
      ring

/-- Arbitrary h is sufficient; no marked-residual, positivity or factor premise. -/
theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport e 2) (he : e = 1 ∨ e = 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound e * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn _ (normalizedSource_supported pIn h),
    response_normalizedSource pOut pIn h]
  exact joint_response_energy pOut pIn he h

/-- The actual projected component supplies the same normalized h and exact energy. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport e 2)
    (he : e = 1 ∨ e = 2) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 3 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound e * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have ht := selected_normalizedSource_energy pOut pIn he h
  rw [henergy, hc]
  exact ht

end AESConcrete.WeightedOutputLineCaps
