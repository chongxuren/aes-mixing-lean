import AESConcrete.TwoOutputThreeUniformGeometry
import AESConcrete.ActivityMinorInput
import AESConcrete.WordFourierBounds
import AESConcrete.WeightedResponse
import AESConcrete.IndexedTripleEnergy
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Exact three-uniform source and the four surviving responses for (8,7)

The actual eight-term signed expansion is stated before the pair/triple
intersections vanish. Every term retains the same arbitrary signed h,
including h(0). The full plane uses the actual two-sided word Fourier
conjugate, whereas the input-zero lines use ordinary resources. Four norms are
added before the single energy square.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoOutputThreeUniformCaps
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOutputThreeUniformGeometry
open AESConcrete.TripleUniformSource (SourceUniformPositions residualLabel source)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform nonzeroUniform_energy zeroUnit)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)

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

def normalizedSource (pIn : SelectedSupport 1 4) (h : AES.Word → ℝ)
    (x : AES.WordState) : ℝ :=
  h (x (residualLabel pIn)) * ∏ j : SourceUniformPositions pIn, nonzeroUniform (x j.val.val)

theorem normalizedSource_source (pIn : SelectedSupport 1 4) (h : AES.Word → ℝ)
    (u : AES.Word) (v : SourceUniformPositions pIn → AES.Word) :
    normalizedSource pIn h (source pIn u v) = h u * ∏ j, nonzeroUniform (v j) := by
  simp only [normalizedSource, TripleUniformSource.source_residual,
    TripleUniformSource.source_uniform]

theorem uniform_tuple_energy (pIn : SelectedSupport 1 4) :
    (∑ v : SourceUniformPositions pIn → AES.Word, (∏ j, nonzeroUniform (v j)) ^ 2) = 1 := by
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum
    (fun _ : SourceUniformPositions pIn => fun u : AES.Word => nonzeroUniform u ^ 2)]
  simp only [nonzeroUniform_energy AES.word_card_gt_one, Finset.prod_const_one]

theorem normalizedSource_energy (pIn : SelectedSupport 1 4) (h : AES.Word → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ u, h u ^ 2 := by
  rw [← (TripleUniformSource.sourceEquiv (V := AES.Word) pIn).sum_comp
    (fun x => normalizedSource pIn h x ^ 2)]
  change (∑ uv : AES.Word × (SourceUniformPositions pIn → AES.Word),
    normalizedSource pIn h (source pIn uv.1 uv.2) ^ 2) = _
  simp_rw [normalizedSource_source, mul_pow]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, uniform_tuple_energy, mul_one]

theorem uniform_product_three (pIn : SelectedSupport 1 4)
    (v : SourceUniformPositions pIn → AES.Word) :
    (∏ j, nonzeroUniform (v j)) =
      nonzeroUniform (v (uniformIndexEquiv pIn 0)) *
      nonzeroUniform (v (uniformIndexEquiv pIn 1)) *
      nonzeroUniform (v (uniformIndexEquiv pIn 2)) := by
  have hp := (uniformIndexEquiv pIn).prod_comp (fun j => nonzeroUniform (v j))
  simpa only [Fin.prod_univ_three, mul_assoc] using hp.symm

def residualKernel (pOut : SelectedSupport 2 2) (y : Retained pOut → AES.Word)
    (c : Plane pOut) : ℝ :=
  ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedEmbedding pOut c i)

def amplitude (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (c : Plane pOut) : ℝ := h (c.val (residualLabel pIn))

def response (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (retainedEmbedding pOut) (fun c => normalizedSource pIn h c.val)

def uniformValue (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) (c : Plane pOut) : AES.Word := c.val j.val.val

theorem response_weightedResponse (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) : response pOut pIn h =
    WeightedResponse.weightedResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn (uniformIndexEquiv pIn 0))
      (uniformValue pOut pIn (uniformIndexEquiv pIn 1))
      (uniformValue pOut pIn (uniformIndexEquiv pIn 2)) := by
  funext y
  unfold response IndexedTripleEnergy.response WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  dsimp only
  rw [show normalizedSource pIn h c.val = h (c.val (residualLabel pIn)) *
    (∏ j : SourceUniformPositions pIn, nonzeroUniform (c.val j.val.val)) from rfl,
    uniform_product_three]
  unfold amplitude residualKernel uniformValue
  ring

theorem omittedWeight_product (pOut : SelectedSupport 2 2) (x : AES.WordState) :
    (∏ j : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 2 pOut) (selectedZeros 2 2 pOut) j (x j.val)) =
      if ∀ i, maskBit pOut.val.val.2 i = true → x i = 0 then 1 else 0 := by
  by_cases hx : ∀ i, maskBit pOut.val.val.2 i = true → x i = 0
  · rw [if_pos hx]
    apply Finset.prod_eq_one
    intro j _
    have hj := output_nonretained_inactive pOut j.val j.property
    simp [nonzeroWeight, selectedZeros, hj, zeroUnit, supportConstant, identityKernel, hx j.val hj]
  · rw [if_neg hx]
    obtain ⟨i, hi, hxi⟩ : ∃ i, maskBit pOut.val.val.2 i = true ∧ x i ≠ 0 := by simpa using hx
    have hE := (output_inactive_iff_not_retained pOut i).mp hi
    apply Finset.prod_eq_zero
      (Finset.mem_univ (⟨i, hE⟩ : GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1))
    simp [nonzeroWeight, selectedZeros, hi, zeroUnit, supportConstant, identityKernel, hxi]

private theorem plane_supported_sum (pOut : SelectedSupport 2 2) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 0 x → F x = 0) :
    (∑ x, F x) = ∑ c : Plane pOut, F c.val := by
  calc
    _ = ∑ x, if graphZeroConditions wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 0 x
        then F x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · exact hF x hx
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _
        (by intro x; simp [ShortenedWeightedGeometry.shortenedSubgroup]) _

/-- Exact physical minor, with both omitted output vectors actual delta-zero units. -/
theorem minorResponse_eq (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    minorResponse (selectedRetained 2 2 pOut) (fun _ => residualMatrix AES.wordSuperboxKernel 0)
      (nonzeroWeight (selectedRetained 2 2 pOut) (selectedZeros 2 2 pOut))
      (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x)) = response pOut pIn h := by
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
    (∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)) *
      (if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
        normalizedSource pIn h x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 0 x → F x = 0 := by
      intro x hx
      have ho : ¬ ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 := by
        intro ho
        exact hx ⟨ho, fun i hi => (empty_mask_no_label i hi).elim⟩
      simp only [F, if_neg ho, mul_zero, zero_mul]
    rw [plane_supported_sum pOut F hF]
    unfold response IndexedTripleEnergy.response
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [F]
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    rw [if_pos ho, mul_one]
    change (∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv c.val i.val)) *
        normalizedSource pIn h c.val = normalizedSource pIn h c.val *
          ∏ i : Retained pOut,
            residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv c.val i.val)
    ring

theorem selectedStep_energy_eq (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut) (normalizedSource pIn h) y ^ 2) =
      ∑ y, response pOut pIn h y ^ 2 := by
  rw [ActivityMinorInput.selectedStepKernel_action, selectedWordTensor_minor_energy,
    minorResponse_eq pOut pIn h]
  exact counting_sum_instances _ _ (fun y : Retained pOut → AES.Word => response pOut pIn h y ^ 2)

theorem amplitude_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) : (∑ c, amplitude pOut pIn h c ^ 2) = q * ∑ u, h u ^ 2 := by
  let j := uniformIndexEquiv pIn 0
  have he := (residualUniformEquiv pOut pIn j).sum_comp
    (fun uv : AES.Word × AES.Word => h uv.1 ^ 2)
  change (∑ c : Plane pOut, amplitude pOut pIn h c ^ 2) =
    ∑ uv : AES.Word × AES.Word, h uv.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, AES.word_card]
  rw [← Finset.mul_sum]
  rfl

/-- Both resources refer to the same actual two-sided word Fourier conjugate. -/
theorem fourier_operator_energy (g : AES.Word → ℝ) :
    (∑ y, action (fourierConjugate WordFourierCore.wordPairing
      (residualMatrix AES.wordSuperboxKernel 0)) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2 := by
  simpa only [WordFourierCore.wordConjugate, WordOrientationClosure.ordinary_word_kernel, rho] using
    WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false g

theorem fourier_column_energy (v : AES.Word) :
    (∑ y, fourierConjugate WordFourierCore.wordPairing
      (residualMatrix AES.wordSuperboxKernel 0) y v ^ 2) ≤ kappa := by
  simpa only [WordFourierCore.wordConjugate, WordOrientationClosure.ordinary_word_kernel, kappa] using
    (WordFourierBounds.fourier_residual_column_energy_lt .ordinary .ordinary false v).le

theorem full_response_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.rawResponse (amplitude pOut pIn h) (residualKernel pOut) y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let dep : Retained pOut := Classical.choice inferInstance
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : Retained pOut => i ≠ dep) rho kappa kappa_nonneg
    fourier_operator_energy fourier_column_energy (retainedEmbedding pOut)
    (retainedEmbedding_injective pOut) (translation pOut pIn)
    (translation_dependent_surjective pOut pIn dep) (amplitude pOut pIn h)
    (amplitude_translation pOut pIn h)
  rw [freeCoordinates_card pOut dep, dependentCoordinates_card pOut dep, pow_one, pow_one,
    amplitude_energy pOut pIn h] at he
  exact he.trans_eq (by ring)

private theorem zeroResponse_eq_line (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn j) =
    IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (lineCurve pOut pIn j) (fun c => h (c.val (residualLabel pIn))) := by
  funext y
  unfold WeightedResponse.zeroResponse uniformValue
  rw [← Finset.sum_filter]
  -- The subtype reindexing preserves both the state and the same signed h.
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Plane pOut => c.val j.val.val = 0),
      amplitude pOut pIn h c * residualKernel pOut y c) =
      ∑ c : {c : Plane pOut // c.val j.val.val = 0},
        amplitude pOut pIn h c.val * residualKernel pOut y c.val from
    Finset.sum_subtype _ (by simp) _]
  rw [← (lineRestrictionEquiv pOut pIn j).symm.sum_comp
    (fun c : {c : Plane pOut // c.val j.val.val = 0} =>
      amplitude pOut pIn h c.val * residualKernel pOut y c.val)]
  rfl

theorem line_response_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn j) y ^ 2) ≤ (rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  rw [zeroResponse_eq_line pOut pIn j h]
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let free : Retained pOut := Classical.choice inferInstance
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2 := by
    intro g
    simpa only [rho] using SharpDampedWordNorm.word_superbox_residual_energy g
  have hc : ∀ v : AES.Word, (∑ y, residualMatrix AES.wordSuperboxKernel 0 y v ^ 2) ≤ kappa := by
    intro v
    simpa only [kappa] using (AllColumnBound.actual_word_residual_column_energy_lt v).le
  have he := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : Retained pOut => i = free) (residualMatrix AES.wordSuperboxKernel 0)
    (lineCurve pOut pIn j) (fun c => h (c.val (residualLabel pIn)))
    (lineRetainedFreeEquiv pOut pIn j free) (lineRetainedFreeEquiv_apply pOut pIn j free)
    rho kappa kappa_nonneg hT hc
  have hdep : Fintype.card (IndexedGraphEnergy.DependentCoordinates
      (fun i : Retained pOut => i = free)) = 1 := by
    rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = free),
      Fintype.card_subtype_eq, retainedCoordinates_card]
  have henergy :
      (∑ c : Line pOut pIn j, h (c.val (residualLabel pIn)) ^ 2) =
        ∑ u : AES.Word, h u ^ 2 := by
    have hs := (Equiv.ofBijective _ (line_residual_bijective pOut pIn j)).sum_comp
      (fun u => h u ^ 2)
    rw [counting_sum_instances (X := Line pOut pIn j) _ inferInstance,
      counting_sum_instances (X := AES.Word) _ inferInstance] at hs
    change (∑ c : Line pOut pIn j, h (c.val (residualLabel pIn)) ^ 2) =
      ∑ u : AES.Word, h u ^ 2 at hs
    exact hs
  rw [counting_sum_instances (X := Line pOut pIn j) _ inferInstance] at he
  simpa only [Finset.prod_const, Finset.card_univ,
    IndexedGraphEnergy.FreeCoordinates, Fintype.card_subtype_eq, hdep, pow_one, henergy] using he

theorem pair_zero_kernel (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (j k : SourceUniformPositions pIn) (hjk : j ≠ k) (y : Retained pOut → AES.Word)
    (c : Plane pOut) (hj : uniformValue pOut pIn j c = 0)
    (hk : uniformValue pOut pIn k c = 0) : residualKernel pOut y c = 0 := by
  have hz := pair_input_zeros pOut pIn j k hjk c hj hk
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  unfold residualKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv c.val i.val) = 0
  rw [hz, map_zero]
  exact AES.word_residual_zero_column (y i)

-- True eight-term expansion: pair/triple responses exist before their vanishing proof.
def pairResponse {S Y : Type*} [Fintype S] (h : S → ℝ) (K : Y → S → ℝ)
    (a b : S → AES.Word) (y : Y) : ℝ :=
  ∑ x, if a x = 0 ∧ b x = 0 then h x * K y x else 0

def tripleResponse {S Y : Type*} [Fintype S] (h : S → ℝ) (K : Y → S → ℝ)
    (a b c : S → AES.Word) (y : Y) : ℝ :=
  ∑ x, if a x = 0 ∧ b x = 0 ∧ c x = 0 then h x * K y x else 0

theorem weightedResponse_eq_eight {S Y : Type*} [Fintype S]
    (h : S → ℝ) (K : Y → S → ℝ) (a b c : S → AES.Word) :
    WeightedResponse.weightedResponse h K a b c = fun y =>
      (WeightedResponse.rawResponse h K y - WeightedResponse.zeroResponse h K a y -
        WeightedResponse.zeroResponse h K b y - WeightedResponse.zeroResponse h K c y +
        pairResponse h K a b y + pairResponse h K a c y + pairResponse h K b c y -
        tripleResponse h K a b c y) / WeightedResponse.normalizer AES.Word := by
  funext y
  have hpoint (x : S) :
      h x * nonzeroUniform (a x) * nonzeroUniform (b x) * nonzeroUniform (c x) * K y x =
      (h x * K y x - (if a x = 0 then h x * K y x else 0) -
        (if b x = 0 then h x * K y x else 0) - (if c x = 0 then h x * K y x else 0) +
        (if a x = 0 ∧ b x = 0 then h x * K y x else 0) +
        (if a x = 0 ∧ c x = 0 then h x * K y x else 0) +
        (if b x = 0 ∧ c x = 0 then h x * K y x else 0) -
        (if a x = 0 ∧ b x = 0 ∧ c x = 0 then h x * K y x else 0)) /
          WeightedResponse.normalizer AES.Word := by
    by_cases ha : a x = 0 <;> by_cases hb : b x = 0 <;> by_cases hc : c x = 0
    <;> simp [nonzeroUniform, supportConstant, identityKernel, ha, hb, hc,
      WeightedResponse.normalizer, div_eq_mul_inv] <;> ring
  unfold WeightedResponse.weightedResponse
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, WeightedResponse.rawResponse,
    WeightedResponse.zeroResponse, pairResponse, tripleResponse]

theorem pairResponse_eq_zero (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (j k : SourceUniformPositions pIn) (hjk : j ≠ k) :
    pairResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn j) (uniformValue pOut pIn k) = 0 := by
  funext y
  unfold pairResponse
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : uniformValue pOut pIn j c = 0 ∧ uniformValue pOut pIn k c = 0
  · simp [hc, pair_zero_kernel pOut pIn j k hjk y c hc.1 hc.2]
  · simp [hc]

theorem tripleResponse_eq_zero (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (j k l : SourceUniformPositions pIn) (hjk : j ≠ k) :
    tripleResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn j) (uniformValue pOut pIn k) (uniformValue pOut pIn l) = 0 := by
  funext y
  unfold tripleResponse
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : uniformValue pOut pIn j c = 0 ∧ uniformValue pOut pIn k c = 0 ∧
      uniformValue pOut pIn l c = 0
  · simp [hc, pair_zero_kernel pOut pIn j k hjk y c hc.1 hc.2.1]
  · simp [hc]

theorem response_eq_four (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) : response pOut pIn h = fun y =>
      (WeightedResponse.rawResponse (amplitude pOut pIn h) (residualKernel pOut) y -
        WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
          (uniformValue pOut pIn (uniformIndexEquiv pIn 0)) y -
        WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
          (uniformValue pOut pIn (uniformIndexEquiv pIn 1)) y -
        WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
          (uniformValue pOut pIn (uniformIndexEquiv pIn 2)) y) /
            WeightedResponse.normalizer AES.Word := by
  have h01 : uniformIndexEquiv pIn 0 ≠ uniformIndexEquiv pIn 1 :=
    fun he => (by omega : (0 : Fin 3) ≠ 1) ((uniformIndexEquiv pIn).injective he)
  have h02 : uniformIndexEquiv pIn 0 ≠ uniformIndexEquiv pIn 2 :=
    fun he => (by omega : (0 : Fin 3) ≠ 2) ((uniformIndexEquiv pIn).injective he)
  have h12 : uniformIndexEquiv pIn 1 ≠ uniformIndexEquiv pIn 2 :=
    fun he => (by omega : (1 : Fin 3) ≠ 2) ((uniformIndexEquiv pIn).injective he)
  rw [response_weightedResponse, weightedResponse_eq_eight,
    pairResponse_eq_zero pOut pIn h _ _ h01, pairResponse_eq_zero pOut pIn h _ _ h02,
    pairResponse_eq_zero pOut pIn h _ _ h12, tripleResponse_eq_zero pOut pIn h _ _ _ h01]
  simp only [Pi.zero_apply, add_zero, sub_zero]

abbrev pieceSquaredBound : ℝ := rho ^ 2 * kappa * (s + 3) ^ 2 / (q - 1) ^ 3

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg rho) kappa_nonneg) (sq_nonneg _))
    (pow_nonneg q_sub_one_pos.le _)

/-- Add the four response norms with their own caps, then square once. -/
theorem response_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  let a : ℝ := rho * Real.sqrt kappa
  have ha : 0 ≤ a := mul_nonneg rho_nonneg (Real.sqrt_nonneg _)
  have ha_sq : a ^ 2 = rho ^ 2 * kappa := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt kappa_nonneg]
  have hfull : (∑ y, WeightedResponse.rawResponse (amplitude pOut pIn h)
      (residualKernel pOut) y ^ 2) ≤ (s * a) ^ 2 * ∑ u, h u ^ 2 :=
    (full_response_energy pOut pIn h).trans_eq (by rw [mul_pow, s_sq, ha_sq]; ring)
  have hline (j : SourceUniformPositions pIn) :
      (∑ y, WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
        (uniformValue pOut pIn j) y ^ 2) ≤ a ^ 2 * ∑ u, h u ^ 2 := by
    simpa only [ha_sq] using line_response_energy pOut pIn j h
  have hl := WeightedResponse.four_response_l2_le
    (WeightedResponse.rawResponse (amplitude pOut pIn h) (residualKernel pOut))
    (WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn (uniformIndexEquiv pIn 0)))
    (WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn (uniformIndexEquiv pIn 1)))
    (WeightedResponse.zeroResponse (amplitude pOut pIn h) (residualKernel pOut)
      (uniformValue pOut pIn (uniformIndexEquiv pIn 2))) h
    (s * a) a a a (WeightedResponse.normalizer AES.Word)
    (mul_nonneg s_pos.le ha) ha ha ha hfull (hline _) (hline _) (hline _)
  -- This rewrite consumes our actual eight-term expansion and vanishing results.
  rw [← response_eq_four pOut pIn h,
    abs_of_nonneg (WeightedResponse.normalizer_nonneg AES.Word)] at hl
  have hcoef : 0 ≤ (s * a + a + a + a) / WeightedResponse.normalizer AES.Word :=
    div_nonneg (by nlinarith [mul_nonneg s_pos.le ha])
      (WeightedResponse.normalizer_nonneg AES.Word)
  have hc : ((s * a + a + a + a) / WeightedResponse.normalizer AES.Word) ^ 2 =
      pieceSquaredBound := by
    rw [div_pow, WeightedResponse.normalizer_sq AES.Word AES.word_card_gt_one.le,
      show s * a + a + a + a = a * (s + 3) by ring, mul_pow, ha_sq, AES.word_card]
    rfl
  have hs := (sq_le_sq₀ (l2_nonneg (response pOut pIn h))
    (mul_nonneg hcoef (l2_nonneg h))).mpr hl
  simpa only [mul_pow, l2_sq, hc] using hs

theorem selected_normalizedSource_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut) (normalizedSource pIn h) y ^ 2) ≤
      pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq]
  exact response_energy pOut pIn h

theorem selected_piece_energy (pOut : SelectedSupport 2 2) (pIn : SelectedSupport 1 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 2 2 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, _, hc, henergy⟩ := TripleUniformSource.word_source_representation pIn f
  have heq : supportIndexComponent (0 : AES.Word) pIn.val f = normalizedSource pIn h := by
    funext x
    have ht := hc (x (residualLabel pIn)) (fun j => x j.val.val)
    rw [TripleUniformSource.source_reconstruct] at ht
    exact ht
  rw [henergy, heq]
  exact selected_normalizedSource_energy pOut pIn h

end AESConcrete.TwoOutputThreeUniformCaps
