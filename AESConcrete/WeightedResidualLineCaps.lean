import AESConcrete.WeightedResidualLineGeometry
import AESConcrete.IndexedTripleEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityMinorInput
import AESConcrete.MultiUniformExpansion
import AESConcrete.UniformGraphCaps
import AESConcrete.ActivityCodeScalar

/-!
# Weighted actual-line source, exact minor and selected energy

Lemmas for (8,9) and (8,6). TwoResidualLine is a source layout template only,
not a theorem premise. The source has one arbitrary signed joint residual h,
one input zero, and 3-e normalized nonzero-uniform legs. The exact selected
minor has two ordinary residual output legs and two delta-zero omitted legs.
On the actual line, pointwise uniform weights supply (q-1)^(-(3-e)); the
separate INPUT residual-tuple injection supplies subenergy. No coordinate
independence or equality with the unrestricted residual energy is assumed.

Constructive AES10/14/16 with independent uniform retained round keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedResidualLineCaps
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedResidualLineGeometry
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
def InputSupported (pIn : SelectedSupport e 3) (G : AES.WordState → ℝ) : Prop :=
  ∀ x, G x ≠ 0 → ∀ i, maskBit pIn.val.val.2 i = true → x i = 0

theorem component_supported (pIn : SelectedSupport e 3) (f : AES.WordState → ℝ) :
    InputSupported pIn (supportIndexComponent (0 : AES.Word) pIn.val f) := by
  intro x hx i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero pIn.val i hi f x hx

/-- Every omitted leg is the actual zero-unit leg, with no uniform weight. -/
theorem omittedWeight_product (pOut : SelectedSupport 2 2) (x : AES.WordState) :
    (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 2 pOut) (selectedZeros 2 2 pOut) j (x j.val)) =
      if ∀ i, maskBit pOut.val.val.2 i = true → x i = 0 then 1 else 0 := by
  by_cases hx : ∀ i, maskBit pOut.val.val.2 i = true → x i = 0
  · rw [if_pos hx]
    apply Finset.prod_eq_one
    intro j _
    have hj := output_nonretained_inactive pOut j.val j.property
    simp [nonzeroWeight, selectedZeros, hj, zeroUnit, supportConstant,
      identityKernel, hx j.val hj]
  · rw [if_neg hx]
    obtain ⟨i, hi, hxi⟩ : ∃ i, maskBit pOut.val.val.2 i = true ∧ x i ≠ 0 := by
      simpa using hx
    have hE := (output_inactive_iff_not_retained pOut i).mp hi
    apply Finset.prod_eq_zero
      (Finset.mem_univ (⟨i, hE⟩ : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1))
    simp [nonzeroWeight, selectedZeros, hi, zeroUnit, supportConstant,
      identityKernel, hxi]

/-- Exact restriction to the physical three-zero line; no normalization is inserted. -/
theorem line_supported_sum (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3) (F : AES.WordState → ℝ)
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
def response (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3) (G : AES.WordState → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => G c.val)

/-- Exact original minor transport, before applying any analytic bound.
The input and output zero conditions are retained in the source subtype. -/
theorem minorResponse_eq (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    minorResponse (selectedRetained 2 2 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 2 2 pOut) (selectedZeros 2 2 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) = response pOut pIn G := by
  unfold selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 2 2 pOut) (selectedZeros 2 2 pOut) j
          (wordMixAddEquiv x j.val)) =
        if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0 :=
    omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x =>
    (∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)) *
      (if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) * G x
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
    rw [if_pos ho, mul_one]
    unfold curve
    ring

/-- The unit omitted output vector preserves exact counting energy. -/
theorem selectedStep_energy_eq (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut) G y ^ 2) =
      ∑ y, response pOut pIn G y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G hG]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn G y ^ 2)

/-- One free operator label and one dependent column, on the same signed code.
The generic theorem has an arbitrary retained index type despite its name. -/
theorem code_response_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
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
abbrev SourceUniformPositions (pIn : SelectedSupport e 3) :=
  MultiUniformExpansion.UniformPositions pIn.val.val.2 pIn.val.val.1

theorem sourceUniformPositions_card (pIn : SelectedSupport e 3) :
    Fintype.card (SourceUniformPositions pIn) = 3 - e.val := by
  have hthree : (3 : Fin 5).val = 3 := rfl
  simpa only [SourceUniformPositions, ← Nat.card_eq_fintype_card, hthree] using
    UniformGraphCaps.selected_uniformPositions_card e 3 pIn

/-- The prescribed normalized source, with one arbitrary signed joint residual. -/
def normalizedSource (pIn : SelectedSupport e 3)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  multiUniform pIn.val.val.2 pIn.val.val.1 h

/-- Only the actual input uniform legs occur in this weight. -/
def uniformWeight (pIn : SelectedSupport e 3) (x : AES.WordState) : ℝ :=
  ∏ i : SourceUniformPositions pIn, nonzeroUniform (x i.val.val)

/-- Public definitions give the exact source split, including its input zero leg.
This is a local derivation; the predecessor's private splitting lemma is unused. -/
theorem normalizedSource_eq (pIn : SelectedSupport e 3)
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
theorem normalizedSource_supported (pIn : SelectedSupport e 3)
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
theorem normalizedSource_on_line (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
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

theorem normalizedSource_energy (pIn : SelectedSupport e 3)
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

abbrev uniformSquaredFactor (e : Fin 5) : ℝ := 1 / (q - 1) ^ (3 - e.val)

theorem uniformSquaredFactor_nonneg (e : Fin 5) : 0 ≤ uniformSquaredFactor e :=
  one_div_nonneg.mpr (pow_nonneg (le_of_lt q_sub_one_pos) _)

/-- Bound each actual physical factor before multiplying; coordinates may correlate. -/
theorem uniformWeight_sq_le (pIn : SelectedSupport e 3) (x : AES.WordState) :
    uniformWeight pIn x ^ 2 ≤ uniformSquaredFactor e := by
  unfold uniformWeight
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _i : SourceUniformPositions pIn, (1 / (q - 1) : ℝ) :=
      Finset.prod_le_prod (fun i _ => sq_nonneg (nonzeroUniform (x i.val.val)))
        (fun i _ => nonzeroUniform_sq_le (x i.val.val))
    _ = (1 / (q - 1) : ℝ) ^ (3 - e.val) := by
      simp only [Finset.prod_const, Finset.card_univ, sourceUniformPositions_card]
    _ = uniformSquaredFactor e := by
      simp only [uniformSquaredFactor, div_pow, one_pow]

def weightedAmplitude (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (h : (Residual pIn → AES.Word) → ℝ) (c : LineCode pOut pIn) : ℝ :=
  h (residualTuple pOut pIn c) * uniformWeight pIn c.val

/-- Pointwise uniform savings and the separate residual INPUT injection compose. -/
theorem weightedAmplitude_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (he : 1 ≤ e.val) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤
      uniformSquaredFactor e * ∑ u, h u ^ 2 := by
  calc
    _ = ∑ c : LineCode pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * uniformWeight pIn c.val ^ 2 := by
      simp only [weightedAmplitude, mul_pow]
    _ ≤ ∑ c : LineCode pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * uniformSquaredFactor e :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (uniformWeight_sq_le pIn c.val) (sq_nonneg _))
    _ = uniformSquaredFactor e *
        ∑ c : LineCode pOut pIn, h (residualTuple pOut pIn c) ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ uniformSquaredFactor e * ∑ u, h u ^ 2 :=
      mul_le_mul_of_nonneg_left (residual_subenergy pOut pIn he h)
        (uniformSquaredFactor_nonneg e)

/-- Raw response with the joint residual and its original physical uniform weights. -/
def jointResponse (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (weightedAmplitude pOut pIn h)

theorem response_normalizedSource (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
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
theorem joint_response_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (he : 1 ≤ e.val) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, jointResponse pOut pIn h y ^ 2) ≤
      pieceSquaredBound e * ∑ u, h u ^ 2 := by
  have hb := code_response_energy pOut pIn (weightedAmplitude pOut pIn h)
  have hw := weightedAmplitude_energy pOut pIn he h
  refine hb.trans ?_
  calc
    (rho ^ 2 * kappa) * ∑ c, weightedAmplitude pOut pIn h c ^ 2 ≤
        (rho ^ 2 * kappa) * (uniformSquaredFactor e * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left hw
        (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg)
    _ = pieceSquaredBound e * ∑ u, h u ^ 2 := by
      unfold pieceSquaredBound uniformSquaredFactor
      ring

/-- Arbitrary h is sufficient; no marked-residual, positivity or factor premise. -/
theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 2)
    (pIn : SelectedSupport e 3) (he : 1 ≤ e.val)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound e * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn _ (normalizedSource_supported pIn h),
    response_normalizedSource pOut pIn h]
  exact joint_response_energy pOut pIn he h

/-- The actual projected component supplies the same normalized h and exact energy. -/
theorem selected_piece_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport e 3)
    (he : 1 ≤ e.val) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound e * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have ht := selected_normalizedSource_energy pOut pIn he h
  rw [henergy, hc]
  exact ht

end AESConcrete.WeightedResidualLineCaps
