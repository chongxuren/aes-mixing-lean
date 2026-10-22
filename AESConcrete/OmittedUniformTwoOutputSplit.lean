import AESConcrete.OmittedUniformTwoOutputBareResponse
import AESConcrete.WeightedOutputLineCaps
import AESConcrete.TwoOutputThreeUniformCaps

/-!
# Exact actual omitted-output split and plane transport

The support indices are (9,7).

The actual selected minor has three normalized nonzero input uniforms and one
normalized nonzero omitted output uniform. Only the latter is split here. The
original arbitrary signed residual-singleton tuple h is preserved, including
h(0). The extra-output-zero term is transported to the (8,7) response
with the same retained labels and an exact tuple-to-scalar amplitude
equivalence.

Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

No plane/line energy for the one-output-zero code, physical factor48 or scalar
certificate is supplied by this finite identity.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoOutputSplit
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoOutputGeometry
  (Retained Residual SourceUniformPositions Code curve residualTuple)
open AESConcrete.OmittedUniformTwoOutputBareResponse (bareKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.WeightedOutputLineCaps (OutputUniformPositions outputUniformWeight)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)

set_option maxRecDepth 100000

-- Finite support facts are placed before the local classical decision instance.
theorem completion_mask_facts : ∀ r : Fin 16, maskSize r = 2 →
    MaskDisjoint (maskComplement r) r ∧ maskSize (maskComplement r) + 2 = 4 := by decide

theorem output_partition : ∀ (pOut : SelectedSupport 2 3)
    (j : OutputUniformPositions pOut) (i : Fin 4),
    maskBit (maskComplement pOut.val.val.1) i = true ↔
      maskBit pOut.val.val.2 i = true ∨ i = j.val.val := by decide

attribute [local instance] Classical.propDecidable

private theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

/-- Preserve the original retained mask and set both other outputs to zero. -/
def zeroCompletion (pOut : SelectedSupport 2 3) : SelectedSupport 2 2 :=
  ⟨⟨(pOut.val.val.1, maskComplement pOut.val.val.1),
    ⟨(completion_mask_facts _ pOut.val.property.2).1, pOut.val.property.2⟩⟩,
    (completion_mask_facts _ pOut.val.property.2).2⟩

theorem zeroCompletion_retained (pOut : SelectedSupport 2 3) :
    (zeroCompletion pOut).val.val.1 = pOut.val.val.1 := rfl

theorem zeroCompletion_zeros (pOut : SelectedSupport 2 3) :
    (zeroCompletion pOut).val.val.2 = maskComplement pOut.val.val.1 := rfl

def omittedIndexEquiv (pOut : SelectedSupport 2 3) : OutputUniformPositions pOut ≃ Fin 1 :=
  Fintype.equivOfCardEq (by
    rw [WeightedOutputLineCaps.outputUniformPositions_card, Fintype.card_fin])

def omittedPosition (pOut : SelectedSupport 2 3) : OutputUniformPositions pOut :=
  (omittedIndexEquiv pOut).symm 0

def omittedLabel (pOut : SelectedSupport 2 3) : Fin 4 := (omittedPosition pOut).val.val

theorem omittedPosition_unique (pOut : SelectedSupport 2 3)
    (j : OutputUniformPositions pOut) : j = omittedPosition pOut := by
  apply (omittedIndexEquiv pOut).injective
  exact Subsingleton.elim _ _

theorem outputUniformWeight_eq (pOut : SelectedSupport 2 3) (x : AES.WordState) :
    outputUniformWeight pOut x = nonzeroUniform (x (omittedLabel pOut)) := by
  have he := (omittedIndexEquiv pOut).symm.prod_comp
    (fun j : OutputUniformPositions pOut => nonzeroUniform (x j.val.val))
  simpa only [Fin.prod_univ_one, omittedPosition, omittedLabel, outputUniformWeight] using he.symm

/-- The accepted singleton-tuple equivalence is used without a centering premise. -/
def scalarAmplitude (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (u : AES.Word) : ℝ :=
  h ((TripleUniformSource.residualTupleEquiv pIn).symm u)

theorem scalarAmplitude_eval (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) :
    scalarAmplitude pIn h (x (TripleUniformSource.residualLabel pIn)) =
      h (fun i : Residual pIn => x i.val) := by
  change h (fun _ => x (TripleUniformSource.residualLabel pIn)) = _
  apply congrArg h
  funext i
  exact (congrArg x (congrArg Subtype.val
    (TripleUniformSource.residualPosition_unique pIn i))).symm

theorem scalarAmplitude_zero (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) : scalarAmplitude pIn h 0 = h 0 := rfl

theorem scalarAmplitude_energy (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ u : AES.Word, scalarAmplitude pIn h u ^ 2) = ∑ v, h v ^ 2 :=
  (TripleUniformSource.residualTupleEquiv pIn).symm.sum_comp (fun v => h v ^ 2)

def normalizedSource (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (x : AES.WordState) : ℝ :=
  h (fun i : Residual pIn => x i.val) *
    ∏ j : SourceUniformPositions pIn, nonzeroUniform (x j.val.val)

theorem normalizedSource_eq_accepted (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    normalizedSource pIn h =
      TwoOutputThreeUniformCaps.normalizedSource pIn (scalarAmplitude pIn h) := by
  funext x
  simp only [normalizedSource, TwoOutputThreeUniformCaps.normalizedSource, scalarAmplitude_eval]

theorem normalizedSource_energy (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ x, normalizedSource pIn h x ^ 2) = ∑ v, h v ^ 2 := by
  rw [normalizedSource_eq_accepted, TwoOutputThreeUniformCaps.normalizedSource_energy,
    scalarAmplitude_energy]

/-- Same retained product on physical states; this only bridges source domains. -/
def stateKernel (pOut : SelectedSupport 2 3) (y : Retained pOut → AES.Word)
    (x : AES.WordState) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv x i.val)

theorem bareKernel_eq_stateKernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    bareKernel pOut pIn y c = stateKernel pOut y c.val := rfl

def omittedValue (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (c : Code pOut pIn) : AES.Word := wordMixAddEquiv c.val (omittedLabel pOut)

/-- W has all three original input uniforms and no omitted-output uniform. -/
def inputWeightedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val * bareKernel pOut pIn y c

/-- R retains the actual omitted output uniform as well as all input uniforms. -/
def omittedResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, normalizedSource pIn h c.val *
    outputUniformWeight pOut (wordMixAddEquiv c.val) * bareKernel pOut pIn y c

def conditionalZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if omittedValue pOut pIn c = 0 then
    normalizedSource pIn h c.val * bareKernel pOut pIn y c else 0

/-- W0 restricts the physical omitted output to zero, with no new normalization. -/
def extraZeroResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : TwoOutputThreeUniformGeometry.Plane (zeroCompletion pOut),
    normalizedSource pIn h c.val * stateKernel pOut y c.val

/-- Identity on physical inputs, now with both omitted outputs constrained. -/
def zeroRestrictionEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4) :
    {c : Code pOut pIn // omittedValue pOut pIn c = 0} ≃
      TwoOutputThreeUniformGeometry.Plane (zeroCompletion pOut) where
  toFun c := ⟨c.val.val, by
    constructor
    · intro i hi
      rcases (output_partition pOut (omittedPosition pOut) i).mp hi with hi | he
      · exact c.val.property.1 i hi
      · rw [he]
        exact c.property
    · intro i hi
      exact (empty_mask_coordinate ⟨i, hi⟩).elim⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · intro i hi
      exact c.property.1 i ((output_partition pOut (omittedPosition pOut) i).mpr (Or.inl hi))
    · intro i hi
      exact (TripleUniformSource.inactiveLabel_not pIn i hi).elim⟩, by
    exact c.property.1 (omittedLabel pOut)
      ((output_partition pOut (omittedPosition pOut) (omittedLabel pOut)).mpr (Or.inr rfl))⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem conditionalZeroResponse_eq_extraZeroResponse
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalZeroResponse pOut pIn h = extraZeroResponse pOut pIn h := by
  funext y
  unfold conditionalZeroResponse extraZeroResponse
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter (fun c : Code pOut pIn => omittedValue pOut pIn c = 0),
      normalizedSource pIn h c.val * bareKernel pOut pIn y c) =
    ∑ c : {c : Code pOut pIn // omittedValue pOut pIn c = 0},
      normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val from
        Finset.sum_subtype _ (by simp) _]
  have he := (zeroRestrictionEquiv pOut pIn).symm.sum_comp
    (fun c : {c : Code pOut pIn // omittedValue pOut pIn c = 0} =>
      normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val)
  change (∑ c : TwoOutputThreeUniformGeometry.Plane (zeroCompletion pOut),
    normalizedSource pIn h c.val * stateKernel pOut y c.val) =
      ∑ c : {c : Code pOut pIn // omittedValue pOut pIn c = 0},
        normalizedSource pIn h c.val.val * bareKernel pOut pIn y c.val at he
  exact he.symm

theorem extraZeroResponse_eq_accepted (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    extraZeroResponse pOut pIn h =
      TwoOutputThreeUniformCaps.response (zeroCompletion pOut) pIn (scalarAmplitude pIn h) := by
  funext y
  unfold extraZeroResponse TwoOutputThreeUniformCaps.response IndexedTripleEnergy.response
  rw [normalizedSource_eq_accepted]
  rfl

theorem extraZeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, extraZeroResponse pOut pIn h y ^ 2) ≤
      TwoOutputThreeUniformCaps.pieceSquaredBound * ∑ v, h v ^ 2 := by
  rw [extraZeroResponse_eq_accepted]
  have he := TwoOutputThreeUniformCaps.response_energy
    (zeroCompletion pOut) pIn (scalarAmplitude pIn h)
  rw [scalarAmplitude_energy] at he
  exact he

def outputNormalizer : ℝ := Real.sqrt ((Fintype.card AES.Word : ℝ) - 1)

theorem outputNormalizer_eq_sqrt_q :
    outputNormalizer = Real.sqrt (ActivityCodeScalar.q - 1) := by
  rw [outputNormalizer, AES.word_card]
  rfl

private theorem omitted_summand (x : AES.Word) (a b : ℝ) :
    a * nonzeroUniform x * b =
      (a * b - (if x = 0 then a * b else 0)) / outputNormalizer := by
  by_cases hx : x = 0 <;>
    simp [nonzeroUniform, supportConstant, identityKernel, hx, outputNormalizer, div_eq_mul_inv]
    <;> ring

/-- Exact omitted-output split; the three input uniforms remain inside W and W0. -/
theorem omittedResponse_eq_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
        Real.sqrt (ActivityCodeScalar.q - 1) := by
  funext y
  rw [← conditionalZeroResponse_eq_extraZeroResponse, ← outputNormalizer_eq_sqrt_q]
  unfold omittedResponse inputWeightedResponse conditionalZeroResponse
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  rw [outputUniformWeight_eq]
  exact omitted_summand (omittedValue pOut pIn c)
    (normalizedSource pIn h c.val) (bareKernel pOut pIn y c)

private theorem code_supported_sum (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (F : AES.WordState → ℝ)
    (hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 pIn.val.val.2 x → F x = 0) :
    (∑ x, F x) = ∑ c : Code pOut pIn, F c.val := by
  calc
    _ = ∑ x, if graphZeroConditions wordMixAddEquiv.toAddMonoidHom
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

/-- The actual physical minor, retaining its original omitted-output factor. -/
def actualResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 3 pOut)
    (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 3 pOut) (selectedZeros 2 3 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
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
    WeightedOutputLineCaps.omittedWeight_product pOut (wordMixAddEquiv x)
  let F : AES.WordState → ℝ := fun x =>
    stateKernel pOut y x *
      ((if ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 then 1 else 0) *
        outputUniformWeight pOut (wordMixAddEquiv x)) * normalizedSource pIn h x
  trans ∑ x, F x
  · apply Finset.sum_congr rfl
    intro x _
    dsimp only [F]
    unfold stateKernel
    unfold selectedRetained at hw
    rw [counting_prod_instances
      (X := GeneralMDSGraphSupport.OtherCoordinates pOut.val.val.1) _ inferInstance,
      hw, counting_prod_instances (X := Retained pOut) _ inferInstance]
  · have hF : ∀ x, ¬ graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2 x → F x = 0 := by
      intro x hx
      have ho : ¬ ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv x i = 0 := by
        intro ho
        exact hx ⟨ho, fun i hi => (TripleUniformSource.inactiveLabel_not pIn i hi).elim⟩
      simp only [F, if_neg ho, zero_mul, mul_zero]
    rw [code_supported_sum pOut pIn F hF]
    unfold omittedResponse
    apply Finset.sum_congr rfl
    intro c _
    have ho : ∀ i, maskBit pOut.val.val.2 i = true → wordMixAddEquiv c.val i = 0 :=
      c.property.1
    dsimp only [F]
    rw [if_pos ho, one_mul, bareKernel_eq_stateKernel]
    ring

/-- R=(W-W0)/sqrt(q-1) for the actual selected minor and original tuple amplitude. -/
theorem actualResponse_eq_split (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        TwoOutputThreeUniformCaps.response (zeroCompletion pOut) pIn (scalarAmplitude pIn h) y) /
          Real.sqrt (ActivityCodeScalar.q - 1) := by
  rw [actualResponse_eq_omittedResponse, omittedResponse_eq_split, extraZeroResponse_eq_accepted]

end AESConcrete.OmittedUniformTwoOutputSplit
