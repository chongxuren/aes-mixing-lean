import AESConcrete.WeightedThreeOutputGeometry
import AESConcrete.ThreeActivePlaneEnergy
import AESConcrete.IndexedTripleEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityMinorInput
import AESConcrete.MultiUniformExpansion
import AESConcrete.ActivityCodeScalar

/-!
# Exact weighted three-output minor and selected energy

Lemmas for (11,5), (11,6), (11,9). Actual input/output zeros are imposed by
the original normalized source and omitted zero-unit leg. The arbitrary signed
joint h never factors. In (11,6), keep one prescribed uniform inside its exact
INPUT-pair parametrization, integrate its square exactly to one, and bound
only the other uniform. No q factor is charged. Output geometry, source
normalization, exact minor and energy have distinct interfaces; physical
factor48 and certificate comparisons belong in StepCaps.

Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WeightedThreeOutputCaps
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.NonzeroUniformGraphCap (zeroUnit nonzeroUniform nonzeroUniform_energy)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.MultiUniformExpansion (multiUniform normalizedLeg InactivePositions)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
variable {e b : Fin 5}

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
def InputSupported (pIn : SelectedSupport e b) (G : AES.WordState → ℝ) : Prop :=
  ∀ x, G x ≠ 0 → ∀ i, maskBit pIn.val.val.2 i = true → x i = 0

theorem component_supported (pIn : SelectedSupport e b) (f : AES.WordState → ℝ) :
    InputSupported pIn (supportIndexComponent (0 : AES.Word) pIn.val f) := by
  intro x hx i hi
  exact MDSGraphSupport.supportIndexComponent_inactive_zero pIn.val i hi f x hx

/-- Every omitted leg is the actual zero-unit leg, with no uniform weight. -/
theorem omittedWeight_product (pOut : SelectedSupport 3 3) (x : AES.WordState) :
    (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut) j (x j.val)) =
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

/-- Exact restriction to the actual zero-constrained code; no normalization is inserted. -/
theorem code_supported_sum (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 x → F x = 0) :
    (∑ x, F x) = ∑ c : Code pOut pIn, F c.val := by
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

/-- Unnormalized three-retained-output response of the actual shortened code. -/
def response (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b) (G : AES.WordState → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => G c.val)

/-- Exact original minor transport, before applying any analytic bound.
The input and output zero conditions are retained in the source subtype. -/
theorem minorResponse_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    minorResponse (selectedRetained 3 3 pOut)
      (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut))
      (fun x => G (wordMixAddEquiv.symm x)) = response pOut pIn G := by
  unfold selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  have hw (x : AES.WordState) :
      (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
        nonzeroWeight (selectedRetained 3 3 pOut) (selectedZeros 3 3 pOut) j
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
    rw [code_supported_sum pOut pIn F hF]
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
theorem selectedStep_energy_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (G : AES.WordState → ℝ) (hG : InputSupported pIn G) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut) G y ^ 2) =
      ∑ y, response pOut pIn G y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action,
    selectedWordTensor_minor_energy, minorResponse_eq pOut pIn G hG]
  exact counting_sum_instances _ _
    (fun y : Retained pOut → AES.Word => response pOut pIn G y ^ 2)

/-- The prescribed normalized source, with one arbitrary signed joint residual. -/
def normalizedSource (pIn : SelectedSupport e b)
    (h : (Residual pIn → AES.Word) → ℝ) : AES.WordState → ℝ :=
  multiUniform pIn.val.val.2 pIn.val.val.1 h

/-- Only the actual input uniform legs occur in this weight. -/
def uniformWeight (pIn : SelectedSupport e b) (x : AES.WordState) : ℝ :=
  ∏ i : SourceUniformPositions pIn, nonzeroUniform (x i.val.val)

/-- Public definitions give the exact source split, including its actual input zero legs.
This is a local derivation; the predecessor's private splitting lemma is unused. -/
theorem normalizedSource_eq (pIn : SelectedSupport e b)
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
theorem normalizedSource_supported (pIn : SelectedSupport e b)
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

/-- The SAME normalized source restricted to the actual code keeps its uniform weights. -/
theorem normalizedSource_on_code (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) :
    normalizedSource pIn h c.val =
      h (residualTuple pOut pIn c) * uniformWeight pIn c.val := by
  rw [normalizedSource_eq]
  have hp : (∏ i : InactivePositions pIn.val.val.2 pIn.val.val.1,
      zeroUnit (c.val i.val.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hz := c.property.2 i.val.val i.property
    simp [zeroUnit, supportConstant, identityKernel, hz]
  rw [hp, mul_one]; rfl

theorem normalizedSource_energy (pIn : SelectedSupport e b)
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

abbrev uniformSquaredFactor (e b : Fin 5) : ℝ := 1 / (q - 1) ^ (b.val - e.val)

theorem uniformSquaredFactor_nonneg (e b : Fin 5) : 0 ≤ uniformSquaredFactor e b :=
  one_div_nonneg.mpr (pow_nonneg (le_of_lt q_sub_one_pos) _)

/-- Bound each actual physical factor before multiplying; coordinates may correlate. -/
theorem uniformWeight_sq_le (pIn : SelectedSupport e b) (x : AES.WordState) :
    uniformWeight pIn x ^ 2 ≤ uniformSquaredFactor e b := by
  unfold uniformWeight
  rw [← Finset.prod_pow]
  calc
    _ ≤ ∏ _i : SourceUniformPositions pIn, (1 / (q - 1) : ℝ) :=
      Finset.prod_le_prod (fun i _ => sq_nonneg (nonzeroUniform (x i.val.val)))
        (fun i _ => nonzeroUniform_sq_le (x i.val.val))
    _ = (1 / (q - 1) : ℝ) ^ (b.val - e.val) := by
      simp only [Finset.prod_const, Finset.card_univ, sourceUniformPositions_card]
    _ = uniformSquaredFactor e b := by
      simp only [uniformSquaredFactor, div_pow, one_pow]

def weightedAmplitude (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (h : (Residual pIn → AES.Word) → ℝ) (c : Code pOut pIn) : ℝ :=
  h (residualTuple pOut pIn c) * uniformWeight pIn c.val

/-- One actual retained operator coordinate and two dependent column labels. -/
theorem code_line_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (mu : Code pOut pIn → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (curve pOut pIn) mu y ^ 2) ≤ (rho ^ 2 * kappa ^ 2) * ∑ c, mu c ^ 2 := by
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
    (curve pOut pIn) mu (lineRetainedFreeEquiv pOut pIn s)
    (lineRetainedFreeEquiv_apply pOut pIn s) rho kappa kappa_nonneg hT hc
  simpa only [Finset.prod_const, Finset.card_univ,
    IndexedGraphEnergy.FreeCoordinates, Fintype.card_subtype_eq,
    line_dependentCoordinates_card pOut s, pow_one] using he

/-- Two actual retained operator coordinates and one dependent column label. -/
theorem code_plane_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport e 3) (mu : Code pOut pIn → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (curve pOut pIn) mu y ^ 2) ≤ (rho ^ 4 * kappa) * ∑ c, mu c ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  exact ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (retainedCoordinates_card pOut) s (curve pOut pIn) mu
    (plane_retained_pair_bijective pOut pIn s)

theorem line_residual_energy (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) = ∑ u, h u ^ 2 :=
  (Equiv.ofBijective _ (line_residualTuple_bijective pOut pIn)).sum_comp (fun u => h u ^ 2)

theorem plane_pair_residual_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) = ∑ u, h u ^ 2 :=
  (Equiv.ofBijective _ (plane_residualTuple_bijective pOut pIn)).sum_comp (fun u => h u ^ 2)

/-- Crucial (11,6) identity: a genuine input pair parametrizes the code, and
the SAME prescribed nonzero uniform has counting squared energy exactly one. -/
theorem residual_uniform_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 3) (s : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : Code pOut pIn,
      h (residualTuple pOut pIn c) ^ 2 * nonzeroUniform (c.val s.val.val) ^ 2) =
        ∑ u, h u ^ 2 := by
  have he := (residualUniformEquiv pOut pIn s).sum_comp
    (fun uv : (Residual pIn → AES.Word) × AES.Word => h uv.1 ^ 2 * nonzeroUniform uv.2 ^ 2)
  change (∑ c : Code pOut pIn,
    h (residualTuple pOut pIn c) ^ 2 * nonzeroUniform (c.val s.val.val) ^ 2) =
      ∑ uv : (Residual pIn → AES.Word) × AES.Word, h uv.1 ^ 2 * nonzeroUniform uv.2 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ y : AES.Word, h u ^ 2 * nonzeroUniform y ^ 2) = h u ^ 2
  rw [← Finset.mul_sum, nonzeroUniform_energy AES.word_card_gt_one, mul_one]

/-- Bound only the other real uniform leg. The retained factor is not replaced
by its supremum, and its physical input label is unchanged. -/
theorem two_uniformWeight_sq_le (pIn : SelectedSupport 1 3)
    (s : SourceUniformPositions pIn) (x : AES.WordState) :
    uniformWeight pIn x ^ 2 ≤
      (1 / (q - 1)) * nonzeroUniform (x s.val.val) ^ 2 := by
  have hcard : (Finset.univ.erase s : Finset (SourceUniformPositions pIn)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
      sourceUniformPositions_card]
    norm_num
  calc
    uniformWeight pIn x ^ 2 = nonzeroUniform (x s.val.val) ^ 2 *
        ∏ i ∈ (Finset.univ.erase s : Finset (SourceUniformPositions pIn)),
          nonzeroUniform (x i.val.val) ^ 2 := by
      unfold uniformWeight
      rw [← Finset.prod_pow]
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ s)).symm
    _ ≤ nonzeroUniform (x s.val.val) ^ 2 *
        ∏ _i ∈ (Finset.univ.erase s : Finset (SourceUniformPositions pIn)), (1 / (q - 1) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun i _ => sq_nonneg (nonzeroUniform (x i.val.val)))
          (fun i _ => nonzeroUniform_sq_le (x i.val.val))) (sq_nonneg _)
    _ = (1 / (q - 1)) * nonzeroUniform (x s.val.val) ^ 2 := by
      rw [Finset.prod_const, hcard, pow_one]
      ring

theorem weightedAmplitude_line_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤ (1 / (q - 1)) * ∑ u, h u ^ 2 := by
  calc
    _ = ∑ c : Code pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * uniformWeight pIn c.val ^ 2 := by
      simp only [weightedAmplitude, mul_pow]
    _ ≤ ∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2 * uniformSquaredFactor 1 2 :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (uniformWeight_sq_le pIn c.val) (sq_nonneg _))
    _ = (1 / (q - 1)) * ∑ u, h u ^ 2 := by
      rw [← Finset.sum_mul, line_residual_energy pOut pIn h]
      norm_num [uniformSquaredFactor] <;> ring

theorem weightedAmplitude_plane_pair_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤ (1 / (q - 1)) * ∑ u, h u ^ 2 := by
  calc
    _ = ∑ c : Code pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * uniformWeight pIn c.val ^ 2 := by
      simp only [weightedAmplitude, mul_pow]
    _ ≤ ∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2 * uniformSquaredFactor 2 3 :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (uniformWeight_sq_le pIn c.val) (sq_nonneg _))
    _ = (1 / (q - 1)) * ∑ u, h u ^ 2 := by
      rw [← Finset.sum_mul, plane_pair_residual_energy pOut pIn h]
      norm_num [uniformSquaredFactor] <;> ring

/-- No q loss: one uniform square integrates to one under the actual INPUT pair. -/
theorem weightedAmplitude_plane_single_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤ (1 / (q - 1)) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  let s : SourceUniformPositions pIn := Classical.choice inferInstance
  calc
    _ = ∑ c : Code pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * uniformWeight pIn c.val ^ 2 := by
      simp only [weightedAmplitude, mul_pow]
    _ ≤ ∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2 *
        ((1 / (q - 1)) * nonzeroUniform (c.val s.val.val) ^ 2) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (two_uniformWeight_sq_le pIn s c.val) (sq_nonneg _))
    _ = (1 / (q - 1)) * ∑ c : Code pOut pIn,
        h (residualTuple pOut pIn c) ^ 2 * nonzeroUniform (c.val s.val.val) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = (1 / (q - 1)) * ∑ u, h u ^ 2 := by
      rw [residual_uniform_energy pOut pIn s h]

def jointResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (weightedAmplitude pOut pIn h)

theorem response_normalizedSource (pOut : SelectedSupport 3 3) (pIn : SelectedSupport e b)
    (h : (Residual pIn → AES.Word) → ℝ) :
    response pOut pIn (normalizedSource pIn h) = jointResponse pOut pIn h := by
  unfold response jointResponse IndexedTripleEnergy.response
  funext y
  apply Finset.sum_congr rfl
  intro c _
  simp only [normalizedSource_on_code, weightedAmplitude]

abbrev linePieceSquaredBound : ℝ := rho ^ 2 * kappa ^ 2 / (q - 1)
abbrev planePieceSquaredBound : ℝ := rho ^ 4 * kappa / (q - 1)

theorem linePieceSquaredBound_nonneg : 0 ≤ linePieceSquaredBound :=
  div_nonneg (mul_nonneg (pow_nonneg rho_nonneg _) (sq_nonneg kappa)) q_sub_one_pos.le

theorem planePieceSquaredBound_nonneg : 0 ≤ planePieceSquaredBound :=
  div_nonneg (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg) q_sub_one_pos.le

theorem joint_line_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, jointResponse pOut pIn h y ^ 2) ≤ linePieceSquaredBound * ∑ u, h u ^ 2 := by
  have hb := code_line_response_energy pOut pIn (weightedAmplitude pOut pIn h)
  have hw := weightedAmplitude_line_energy pOut pIn h
  refine hb.trans ?_
  calc
    _ ≤ (rho ^ 2 * kappa ^ 2) * ((1 / (q - 1)) * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg (pow_nonneg rho_nonneg _) (sq_nonneg kappa))
    _ = _ := by unfold linePieceSquaredBound; ring

theorem joint_plane_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport e 3) (he : e = 1 ∨ e = 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, jointResponse pOut pIn h y ^ 2) ≤ planePieceSquaredBound * ∑ u, h u ^ 2 := by
  have hw : (∑ c, weightedAmplitude pOut pIn h c ^ 2) ≤ (1 / (q - 1)) * ∑ u, h u ^ 2 := by
    rcases he with rfl | rfl
    · exact weightedAmplitude_plane_single_energy pOut pIn h
    · exact weightedAmplitude_plane_pair_energy pOut pIn h
  refine (code_plane_response_energy pOut pIn (weightedAmplitude pOut pIn h)).trans ?_
  calc
    _ ≤ (rho ^ 4 * kappa) * ((1 / (q - 1)) * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg)
    _ = _ := by unfold planePieceSquaredBound; ring

theorem selected_normalizedSource_line_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ linePieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn _ (normalizedSource_supported pIn h),
    response_normalizedSource pOut pIn h]
  exact joint_line_response_energy pOut pIn h

theorem selected_normalizedSource_plane_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport e 3) (he : e = 1 ∨ e = 2)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ planePieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn _ (normalizedSource_supported pIn h),
    response_normalizedSource pOut pIn h]
  exact joint_plane_response_energy pOut pIn he h

/-- The original projected component supplies exactly the same normalized h. -/
theorem selected_piece_line_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 2) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      linePieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have ht := selected_normalizedSource_line_energy pOut pIn h
  rw [henergy, hc]
  exact ht

theorem selected_piece_plane_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport e 3) (he : e = 1 ∨ e = 2) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      planePieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have ht := selected_normalizedSource_plane_energy pOut pIn he h
  rw [henergy, hc]
  exact ht

end AESConcrete.WeightedThreeOutputCaps

