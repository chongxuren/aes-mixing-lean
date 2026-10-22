import AESConcrete.OmittedPairOneInputSource
import AESConcrete.FiniteTensorEnergy
import AESConcrete.SharpDampedWordNorm

/-!
Lemmas for (10,9). Each restriction is identity on physical states. Residual-
input bijections and retained-output bijections serve separate purposes. The
single-output restriction keeps the original input U and inserts no output U.
The double-output restriction is exactly the weighted-line response,
with original h and original input masks. No (9,10) endpoint is a premise.
Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedPairOneInputEvents
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedPairOneInputRawGeometry
open AESConcrete.OmittedPairOneInputSource
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
set_option maxRecDepth 100000

-- These proofs concern only finite physical support masks, never word states.
theorem completion_mask_facts : ∀ r : Fin 16, maskSize r = 2 →
    MaskDisjoint (maskComplement r) r ∧ maskSize (maskComplement r) + 2 = 4 := by decide

theorem omitted_pair_partition : ∀ (pOut : SelectedSupport 2 4)
    (a b : Omitted pOut), a ≠ b → ∀ i : Fin 4,
    maskBit (maskComplement pOut.val.val.1) i = true ↔ i = a.val ∨ i = b.val := by decide

attribute [local instance] Classical.propDecidable

abbrev RestrictedCode (pIn : SelectedSupport 2 3) (r z : Fin 16) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom r z

def restrictedCurve (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3) (r z : Fin 16)
    (c : RestrictedCode pIn r z) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def restrictedResidual (pIn : SelectedSupport 2 3) (r z : Fin 16)
    (c : RestrictedCode pIn r z) : Residual pIn → AES.Word := fun i => c.val i.val

/-- A reusable identity-on-state restriction equivalence. -/
def restrictionEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (r z : Fin 16) (Q : Code pOut pIn → Prop) [DecidablePred Q]
    (hz : ∀ i, maskBit pIn.val.val.2 i = true → maskBit z i = true)
    (hQ : ∀ c : Code pOut pIn, Q c ↔
      graphZeroConditions wordMixAddEquiv.toAddMonoidHom r z c.val) :
    {c : Code pOut pIn // Q c} ≃ RestrictedCode pIn r z where
  toFun c := ⟨c.val.val, (hQ c.val).mp c.property⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · intro i hi
      exact (output_inactive_not pOut i hi).elim
    · intro i hi
      exact c.property.2 i (hz i hi)⟩, (hQ _).mpr c.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem conditional_response_eq (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (r z : Fin 16) (Q : Code pOut pIn → Prop) [DecidablePred Q]
    (hz : ∀ i, maskBit pIn.val.val.2 i = true → maskBit z i = true)
    (hQ : ∀ c : Code pOut pIn, Q c ↔
      graphZeroConditions wordMixAddEquiv.toAddMonoidHom r z c.val)
    (G : AES.WordState → ℝ) (y : Retained pOut → AES.Word) :
    (∑ c : Code pOut pIn, if Q c then G c.val * bareKernel pOut pIn y c else 0) =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (restrictedCurve pOut pIn r z) (fun c => G c.val) y := by
  rw [← Finset.sum_filter]
  rw [show (∑ c ∈ Finset.univ.filter Q, G c.val * bareKernel pOut pIn y c) =
      ∑ c : {c : Code pOut pIn // Q c},
        G c.val.val * bareKernel pOut pIn y c.val from
          Finset.sum_subtype _ (by simp) _]
  exact (restrictionEquiv pOut pIn r z Q hz hQ).sum_comp
    (fun c : RestrictedCode pIn r z => G c.val *
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i)
        (restrictedCurve pOut pIn r z c i))

/-- Ordinary pair tensorization on an actual retained-coordinate bijection. -/
theorem response_energy_of_bijective (pOut : SelectedSupport 2 4)
    {C : Type*} [Fintype C] (v : C → Retained pOut → AES.Word)
    (hv : Function.Bijective v) (mu : C → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) v mu y ^ 2) ≤
      rho ^ 4 * ∑ c, mu c ^ 2 := by
  let e : C ≃ (Retained pOut → AES.Word) := Equiv.ofBijective v hv
  let f : (Retained pOut → AES.Word) → ℝ := fun z => mu (e.symm z)
  have hf : (∑ z, f z ^ 2) = ∑ c, mu c ^ 2 := e.symm.sum_comp (fun c => mu c ^ 2)
  have hr (y : Retained pOut → AES.Word) :
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) v mu y =
        action (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0)) f y := by
    unfold IndexedTripleEnergy.response action coordinateKernel
    rw [← e.symm.sum_comp (fun c => mu c * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (v c i))]
    apply Finset.sum_congr rfl
    intro z _
    have hz : v (e.symm z) = z := e.apply_symm_apply z
    rw [hz]
    exact mul_comm _ _
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2 := by
    intro g
    simpa only [rho] using SharpDampedWordNorm.word_superbox_residual_energy g
  have he := FiniteTensorEnergy.uniform_coordinate_energy
    (residualMatrix AES.wordSuperboxKernel 0) rho hT f
  simp_rw [← hr] at he
  rw [hf] at he
  have hc := retainedCoordinates_card pOut
  simp only [← Nat.card_eq_fintype_card] at he hc
  rw [hc] at he
  exact he

def inputZeroMask (pIn : SelectedSupport 2 3) : Fin 16 :=
  maskUnion pIn.val.val.2 (singletonMask (inputUniform pIn).val.val)

theorem inputZeroMask_size (pIn : SelectedSupport 2 3) : maskSize (inputZeroMask pIn) = 2 := by
  have hz : MaskDisjoint pIn.val.val.2 (singletonMask (inputUniform pIn).val.val) := by
    intro i hi hu
    have he := (singletonMask_bit _ _).mp hu
    subst i
    exact (inputUniform pIn).property hi
  rw [inputZeroMask, maskUnion_size _ _ hz, inputInactiveMask_size, singletonMask_size]

theorem inputZeroMask_residual_disjoint (pIn : SelectedSupport 2 3) :
    MaskDisjoint (inputZeroMask pIn) pIn.val.val.1 := by
  intro i hz hj
  rw [inputZeroMask, maskUnion_bit, Bool.or_eq_true] at hz
  rcases hz with hz | hu
  · exact pIn.val.property.1 i hz hj
  · have he := (singletonMask_bit _ _).mp hu
    subst i
    exact (inputUniform pIn).val.property hj

theorem input_zero_conditions (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (c : Code pOut pIn) : c.val (inputUniform pIn).val.val = 0 ↔
      graphZeroConditions wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (inputZeroMask pIn) c.val := by
  constructor
  · intro hu
    refine ⟨c.property.1, ?_⟩
    intro i hi
    rw [inputZeroMask, maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hz | hu'
    · exact c.property.2 i hz
    · rw [(singletonMask_bit _ _).mp hu']
      exact hu
  · intro hc
    apply hc.2 (inputUniform pIn).val.val
    rw [inputZeroMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inr ((singletonMask_bit _ _).mpr rfl)

theorem input_zero_response_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputZeroResponse pOut pIn h y ^ 2) ≤ rho ^ 4 * ∑ r, h r ^ 2 := by
  let z := inputZeroMask pIn
  have hsize : maskSize pOut.val.val.2 + maskSize z + maskSize pOut.val.val.1 = 4 := by
    rw [outputInactiveMask_size, inputZeroMask_size, retainedMask_size]
  have ho := (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS pOut.val.val.2 z pOut.val.val.1 pOut.val.property.1 hsize).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have hsize' : maskSize pOut.val.val.2 + maskSize z + maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, inputZeroMask_size, residualMask_size]
  have hi := (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS pOut.val.val.2 z pIn.val.val.1
    (inputZeroMask_residual_disjoint pIn) hsize').comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have henergy := (Equiv.ofBijective (restrictedResidual pIn pOut.val.val.2 z) hi).sum_comp
    (fun r => h r ^ 2)
  -- Expose the equivalence's forward function before rewriting the source energy.
  change (∑ c : RestrictedCode pIn pOut.val.val.2 z,
    h (restrictedResidual pIn pOut.val.val.2 z c) ^ 2) = ∑ r, h r ^ 2 at henergy
  have he := response_energy_of_bijective pOut (restrictedCurve pOut pIn pOut.val.val.2 z) ho
    (fun c => h (restrictedResidual pIn pOut.val.val.2 z c))
  rw [henergy] at he
  have hr : inputZeroResponse pOut pIn h =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (restrictedCurve pOut pIn pOut.val.val.2 z)
        (fun c => h (restrictedResidual pIn pOut.val.val.2 z c)) := by
    funext y
    exact conditional_response_eq pOut pIn _ z
      (fun c => c.val (inputUniform pIn).val.val = 0)
      (by
        intro i hi
        -- Expose the let-bound z as a concrete union before applying its bit theorem.
        change maskBit (maskUnion pIn.val.val.2
          (singletonMask (inputUniform pIn).val.val)) i = true
        rw [maskUnion_bit, Bool.or_eq_true]
        exact Or.inl hi)
      (input_zero_conditions pOut pIn) (fun x => h (fun i => x i.val)) y
  rw [hr]
  exact he

/-- One omitted output zero plus the ORIGINAL input zero is a plane. -/
theorem single_output_conditions (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (c : Code pOut pIn) : outputValue pOut pIn a c = 0 ↔
      graphZeroConditions wordMixAddEquiv.toAddMonoidHom (singletonMask a.val) pIn.val.val.2 c.val := by
  constructor
  · intro ha
    refine ⟨?_, c.property.2⟩
    intro i hi
    rw [(singletonMask_bit _ _).mp hi]
    exact ha
  · intro hc
    exact hc.1 a.val ((singletonMask_bit _ _).mpr rfl)

theorem single_output_amplitude_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : RestrictedCode pIn (singletonMask a.val) pIn.val.val.2,
      normalizedSource pIn h c.val ^ 2) ≤ (1 / (q - 1)) * ∑ r, h r ^ 2 := by
  have hs : maskSize (singletonMask a.val) + maskSize pIn.val.val.2 + maskSize pIn.val.val.1 = 4 := by
    rw [singletonMask_size, inputInactiveMask_size, residualMask_size]
  have hi := (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ pIn.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have hr := (Equiv.ofBijective (restrictedResidual pIn (singletonMask a.val) pIn.val.val.2) hi).sum_comp
    (fun r => h r ^ 2)
  change (∑ c : RestrictedCode pIn (singletonMask a.val) pIn.val.val.2,
    h (restrictedResidual pIn (singletonMask a.val) pIn.val.val.2 c) ^ 2) = ∑ r, h r ^ 2 at hr
  calc
    _ ≤ ∑ c : RestrictedCode pIn (singletonMask a.val) pIn.val.val.2,
        h (restrictedResidual pIn _ _ c) ^ 2 * (1 / (q - 1)) := by
      apply Finset.sum_le_sum
      intro c _
      let c0 : Code pOut pIn := ⟨c.val, by
        constructor
        · intro i hi
          exact (output_inactive_not pOut i hi).elim
        · exact c.property.2⟩
      have hc := normalizedSource_on_code pOut pIn h c0
      rw [hc, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (WeightedResidualLineCaps.nonzeroUniform_sq_le _) (sq_nonneg _)
    _ = (1 / (q - 1)) * ∑ r, h r ^ 2 := by
      rw [← Finset.sum_mul, hr]
      ring

theorem single_output_response_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputZeroResponse pOut pIn a h y ^ 2) ≤
      (rho ^ 4 / (q - 1)) * ∑ r, h r ^ 2 := by
  have hd : MaskDisjoint (singletonMask a.val) pOut.val.val.1 := by
    intro i hi hj
    have he := (singletonMask_bit _ _).mp hi
    subst i
    exact a.property hj
  have hs : maskSize (singletonMask a.val) + maskSize pIn.val.val.2 + maskSize pOut.val.val.1 = 4 := by
    rw [singletonMask_size, inputInactiveMask_size, retainedMask_size]
  have ho := (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hd hs).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have he := response_energy_of_bijective pOut
    (restrictedCurve pOut pIn (singletonMask a.val) pIn.val.val.2) ho
    (fun c => normalizedSource pIn h c.val)
  have hr : outputZeroResponse pOut pIn a h =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (restrictedCurve pOut pIn (singletonMask a.val) pIn.val.val.2)
        (fun c => normalizedSource pIn h c.val) := by
    funext y
    exact conditional_response_eq pOut pIn _ _ (fun c => outputValue pOut pIn a c = 0)
      (fun _ hi => hi) (single_output_conditions pOut pIn a) (normalizedSource pIn h) y
  rw [hr]
  exact he.trans ((mul_le_mul_of_nonneg_left (single_output_amplitude_energy pOut pIn a h)
    (pow_nonneg (by norm_num [rho]) _)).trans_eq (by ring))

/-- Same retained labels; exactly the two omitted outputs become inactive. -/
def zeroCompletion (pOut : SelectedSupport 2 4) : SelectedSupport 2 2 :=
  ⟨⟨(pOut.val.val.1, maskComplement pOut.val.val.1),
    ⟨(completion_mask_facts _ pOut.val.property.2).1, pOut.val.property.2⟩⟩,
    (completion_mask_facts _ pOut.val.property.2).2⟩

theorem double_output_conditions (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 2 3)
    (c : Code pOut pIn) :
    (outputValue pOut pIn (omittedFirst pOut) c = 0 ∧
      outputValue pOut pIn (omittedSecond pOut) c = 0) ↔
      graphZeroConditions wordMixAddEquiv.toAddMonoidHom
        (maskComplement pOut.val.val.1) pIn.val.val.2 c.val := by
  constructor
  · intro hab
    refine ⟨?_, c.property.2⟩
    intro i hi
    rcases (omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) i).mp hi with ha | hb
    · rw [ha]; exact hab.1
    · rw [hb]; exact hab.2
  · intro hc
    constructor
    · exact hc.1 _ ((omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) _).mpr (Or.inl rfl))
    · exact hc.1 _ ((omitted_pair_partition pOut _ _ (omittedFirst_ne_second pOut) _).mpr (Or.inr rfl))

/-- Exact identity, before using the admitted weighted-line quantitative bound. -/
theorem outputIntersection_eq_jointResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    outputIntersectionResponse pOut pIn h =
      WeightedResidualLineCaps.jointResponse (zeroCompletion pOut) pIn h := by
  funext y
  have he := conditional_response_eq pOut pIn (maskComplement pOut.val.val.1) pIn.val.val.2
    (fun c => outputValue pOut pIn (omittedFirst pOut) c = 0 ∧
      outputValue pOut pIn (omittedSecond pOut) c = 0)
    (fun _ hi => hi) (double_output_conditions pOut pIn) (normalizedSource pIn h) y
  change outputIntersectionResponse pOut pIn h y = _ at he
  rw [he]
  have hr := congrFun (WeightedResidualLineCaps.response_normalizedSource
    (zeroCompletion pOut) pIn h) y
  exact hr

theorem double_output_response_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 2 3) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, outputIntersectionResponse pOut pIn h y ^ 2) ≤
      (rho ^ 2 * kappa / (q - 1)) * ∑ r, h r ^ 2 := by
  rw [outputIntersection_eq_jointResponse]
  have he := WeightedResidualLineCaps.joint_response_energy
    (zeroCompletion pOut) pIn (by decide) h
  -- Normalize both counting spaces; the provider also carries its own output instance.
  have hsumOutput (a b : Fintype (Retained pOut → AES.Word)) :
      (letI := a; ∑ y, WeightedResidualLineCaps.jointResponse (zeroCompletion pOut) pIn h y ^ 2) =
        (letI := b; ∑ y, WeightedResidualLineCaps.jointResponse (zeroCompletion pOut) pIn h y ^ 2) := by
    have hab : a = b := Subsingleton.elim _ _
    cases hab
    rfl
  have hsum (a b : Fintype (Residual pIn → AES.Word)) :
      (letI := a; ∑ r, h r ^ 2) = (letI := b; ∑ r, h r ^ 2) := by
    have hab : a = b := Subsingleton.elim _ _
    cases hab
    rfl
  simp only [WeightedResidualLineCaps.pieceSquaredBound,
    show 3 - (2 : Fin 5).val = 1 by decide, pow_one] at he
  -- Goal-directed equalities fix the counting instances from both endpoints.
  convert he using 1 <;>
    first
    | rfl
    | exact hsumOutput _ _
    | exact congrArg (fun E : ℝ => (rho ^ 2 * kappa / (q - 1)) * E) (hsum _ _)
end AESConcrete.OmittedPairOneInputEvents
