import AESConcrete.TwoOmittedTwoInputSource
import AESConcrete.TwoOmittedTwoInputScalar
import AESConcrete.FiniteTensorEnergy
import AESConcrete.SharpDampedWordNorm

/-!
Lemmas for (10,10). Full raw cancellation is an exact mixed-information-set
identity. Both single input-zero raw events retain q source multiplicity and q
fiber Cauchy. The double input-zero event uses a separate ordinary retained-
pair bijection. The original signed JOINT h, including zero, is unchanged in
every event. Constructive fixed AES10/14/16 only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedTwoInputInputEnergy
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedTwoInputSource
open AESConcrete.TwoOmittedTwoInputScalar
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.UniformGraphScalar (rho)
open AESConcrete.ActivityCodeScalar (q)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

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

abbrev FullCode (pOut pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

def stateCodeEquiv (pOut pIn : SelectedSupport 2 4) : AES.WordState ≃ FullCode pOut pIn where
  toFun x := ⟨x, by
    constructor
    · intro i hi; exact (empty_inactive pOut i hi).elim
    · intro i hi; exact (empty_inactive pIn i hi).elim⟩
  invFun c := c.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def fullMixedEquiv (pOut pIn : SelectedSupport 2 4) :
    AES.WordState ≃ (Residual pIn → AES.Word) × (Retained pOut → AES.Word) := by
  have hs : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 +
      maskSize pOut.val.val.1 + maskSize pIn.val.val.1 = 4 := by
    rw [OmittedUniformTwoInputRawGeometry.inputInactiveMask_size,
      OmittedUniformTwoInputRawGeometry.inputInactiveMask_size, retainedMask_size, retainedMask_size]
  exact (stateCodeEquiv pOut pIn).trans
    ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
      (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
        wordMixAddEquiv_zeroMDS _ _ _ _ pOut.val.property.1 pIn.val.property.1 hs))

@[simp] theorem fullMixedEquiv_fst (pOut pIn : SelectedSupport 2 4) (x : AES.WordState) :
    (fullMixedEquiv pOut pIn x).1 = fun i : Residual pIn => x i.val := rfl
@[simp] theorem fullMixedEquiv_snd (pOut pIn : SelectedSupport 2 4) (x : AES.WordState) :
    (fullMixedEquiv pOut pIn x).2 = fun i : Retained pOut => wordMixAddEquiv x i.val := rfl

/-- Row sums, not a centering hypothesis on h, annihilate the raw full term. -/
theorem rawResponse_eq_zero (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : rawResponse pOut pIn h = 0 := by
  funext y
  change (∑ x : AES.WordState, h (fun i => x i.val) * bareKernel pOut y x) = 0
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let i0 : Retained pOut := Classical.choice inferInstance
  have hrow : (∑ z : Retained pOut → AES.Word,
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (z i)) = 0 := by
    rw [← Fintype.prod_sum (fun i : Retained pOut => fun v : AES.Word =>
      residualMatrix AES.wordSuperboxKernel 0 (y i) v)]
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    exact WordMixedCentering.residual_row_sum AES.wordSuperboxKernel AES.word_superbox_pointed (y i0)
  calc
    _ = ∑ p : (Residual pIn → AES.Word) × (Retained pOut → AES.Word),
        h p.1 * ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (p.2 i) :=
      (fullMixedEquiv pOut pIn).sum_comp
        (fun p => h p.1 * ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (p.2 i))
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro r _
      simp only [Prod.fst, Prod.snd]
      rw [← Finset.mul_sum, hrow, mul_zero]

def singleRestrictionEquiv (pOut pIn : SelectedSupport 2 4) (t : InputUniformPositions pIn) :
    {x : AES.WordState // x t.val.val = 0} ≃
      TwoOmittedTwoInputSingleRawGeometry.Code pOut (singleInput pIn t) where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi; exact (empty_inactive pOut i hi).elim
    · intro i hi
      change maskBit (singletonMask t.val.val) i = true at hi
      rw [(singletonMask_bit _ _).mp hi]
      exact x.property⟩
  invFun c := ⟨c.val, c.property.2 t.val.val ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem inputZero_eq_singleRaw (pOut pIn : SelectedSupport 2 4) (t : InputUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputZeroResponse pOut pIn t h =
      TwoOmittedTwoInputSingleRawEnergy.rawFullResponse pOut (singleInput pIn t) h := by
  funext y
  unfold inputZeroResponse WeightedResponse.zeroResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState => x t.val.val = 0),
      h (fun i => x i.val) * bareKernel pOut y x) =
      ∑ x : {x : AES.WordState // x t.val.val = 0}, h (fun i => x.val i.val) * bareKernel pOut y x.val from
        Finset.sum_subtype _ (by simp) _]
  exact (singleRestrictionEquiv pOut pIn t).sum_comp
    (fun c => h (TwoOmittedTwoInputSingleRawGeometry.residualTuple pOut (singleInput pIn t) c) *
      ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i)
        (wordMixAddEquiv c.val i.val))

theorem inputZero_energy (pOut pIn : SelectedSupport 2 4) (t : InputUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputZeroResponse pOut pIn t h y ^ 2) ≤ fullRawNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [inputZero_eq_singleRaw]
  exact (TwoOmittedTwoInputSingleRawEnergy.rawFullResponse_energy pOut (singleInput pIn t) h).trans
    (mul_le_mul_of_nonneg_right full_energy_coefficient_le
      (Finset.sum_nonneg (fun r _ => sq_nonneg (h r))))

def doubleInputMask (pIn : SelectedSupport 2 4) :=
  maskUnion (singletonMask (uniformFirst pIn).val.val) (singletonMask (uniformSecond pIn).val.val)

abbrev DoubleCode (pOut pIn : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (doubleInputMask pIn)

theorem doubleInputMask_size (pIn : SelectedSupport 2 4) : maskSize (doubleInputMask pIn) = 2 := by
  have hd : MaskDisjoint (singletonMask (uniformFirst pIn).val.val)
      (singletonMask (uniformSecond pIn).val.val) := by
    intro i hi hj
    have he : (uniformFirst pIn).val.val = (uniformSecond pIn).val.val :=
      ((singletonMask_bit _ _).mp hi).symm.trans ((singletonMask_bit _ _).mp hj)
    exact OmittedUniformTwoInputPairSource.uniformFirst_ne_second pIn (Subtype.ext (Subtype.ext he))
  rw [doubleInputMask, maskUnion_size _ _ hd, singletonMask_size, singletonMask_size]

theorem doubleInputMask_disjoint (pIn : SelectedSupport 2 4) :
    MaskDisjoint (doubleInputMask pIn) pIn.val.val.1 := by
  intro i hi hj
  rw [doubleInputMask, maskUnion_bit, Bool.or_eq_true] at hi
  rcases hi with hu | hv
  · have he := (singletonMask_bit _ _).mp hu
    subst i
    exact (uniformFirst pIn).val.property hj
  · have he := (singletonMask_bit _ _).mp hv
    subst i
    exact (uniformSecond pIn).val.property hj

def doubleRestrictionEquiv (pOut pIn : SelectedSupport 2 4) :
    {x : AES.WordState // x (uniformFirst pIn).val.val = 0 ∧ x (uniformSecond pIn).val.val = 0} ≃
      DoubleCode pOut pIn where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi; exact (empty_inactive pOut i hi).elim
    · intro i hi
      rw [doubleInputMask, maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hu | hv
      · rw [(singletonMask_bit _ _).mp hu]; exact x.property.1
      · rw [(singletonMask_bit _ _).mp hv]; exact x.property.2⟩
  invFun c := ⟨c.val, by
    constructor
    · apply c.property.2
      rw [doubleInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl ((singletonMask_bit _ _).mpr rfl)
    · apply c.property.2
      rw [doubleInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inr ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def doubleCurve (pOut pIn : SelectedSupport 2 4) (c : DoubleCode pOut pIn) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def doubleResidual (pOut pIn : SelectedSupport 2 4) (c : DoubleCode pOut pIn) : Residual pIn → AES.Word :=
  fun i => c.val i.val

theorem inputIntersection_eq_response (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputIntersectionResponse pOut pIn h = IndexedTripleEnergy.response
      (residualMatrix AES.wordSuperboxKernel 0) (doubleCurve pOut pIn) (fun c => h (doubleResidual pOut pIn c)) := by
  funext y
  unfold inputIntersectionResponse TripleResponse.intersectionResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState =>
      x (uniformFirst pIn).val.val = 0 ∧ x (uniformSecond pIn).val.val = 0),
      h (fun i => x i.val) * bareKernel pOut y x) =
      ∑ x : {x : AES.WordState // x (uniformFirst pIn).val.val = 0 ∧ x (uniformSecond pIn).val.val = 0},
        h (fun i => x.val i.val) * bareKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (doubleRestrictionEquiv pOut pIn).sum_comp
    (fun c => h (doubleResidual pOut pIn c) * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (doubleCurve pOut pIn c i))

theorem inputIntersection_energy (pOut pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputIntersectionResponse pOut pIn h y ^ 2) ≤ eventRawNorm ^ 2 * ∑ r, h r ^ 2 := by
  have hs : maskSize pOut.val.val.2 + maskSize (doubleInputMask pIn) + maskSize pOut.val.val.1 = 4 := by
    rw [OmittedUniformTwoInputRawGeometry.inputInactiveMask_size, doubleInputMask_size, retainedMask_size]
  have ho := (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ pOut.val.property.1 hs).comp (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have hs' : maskSize pOut.val.val.2 + maskSize (doubleInputMask pIn) + maskSize pIn.val.val.1 = 4 := by
    rw [OmittedUniformTwoInputRawGeometry.inputInactiveMask_size, doubleInputMask_size, retainedMask_size]
  have hi := (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ (doubleInputMask_disjoint pIn) hs').comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  have hr := (Equiv.ofBijective (doubleResidual pOut pIn) hi).sum_comp (fun r => h r ^ 2)
  change (∑ c : DoubleCode pOut pIn, h (doubleResidual pOut pIn c) ^ 2) =
    ∑ r, h r ^ 2 at hr
  rw [inputIntersection_eq_response, ← event_energy_coefficient_eq]
  exact (response_energy_of_bijective pOut (doubleCurve pOut pIn) ho
    (fun c => h (doubleResidual pOut pIn c))).trans_eq (by rw [hr])
end AESConcrete.TwoOmittedTwoInputInputEnergy
