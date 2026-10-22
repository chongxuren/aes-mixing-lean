import AESConcrete.OmittedUniformTwoInputPairSource
import AESConcrete.OmittedUniformTwoInputRawGeometry
import AESConcrete.TripleResponse
import AESConcrete.IndexedTripleEnergy

/-!
# Actual singleton/double input-zero geometry for (9,10)

RawGeometry and PairSource supply the source interfaces. The same original
joint residual-pair h, including h(0,0), is used in every event. A singleton
zero plane has bijective retained and JOINT residual pairs. A double-zero line
has only residual subenergy; no residual-pair surjectivity is claimed.
Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.

No scalar comparison, selected-minor estimate or physical aggregation is
supplied here.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformPairEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.OmittedUniformTwoInputPairSource (bareKernel)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
set_option maxRecDepth 100000

theorem inputInactiveMask_eq_zero :
    ∀ pIn : SelectedSupport 2 4, pIn.val.val.2 = 0 := by decide

theorem maskUnion_zero_left : ∀ z : Fin 16, maskUnion 0 z = z := by decide

attribute [local instance] Classical.propDecidable

def eventInputMask (pIn : SelectedSupport 2 4) (z : Fin 16) : Fin 16 :=
  maskUnion pIn.val.val.2 z

theorem eventInputMask_eq (pIn : SelectedSupport 2 4) (z : Fin 16) :
    eventInputMask pIn z = z := by
  simpa only [eventInputMask, inputInactiveMask_eq_zero] using maskUnion_zero_left z

abbrev EventCode (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (eventInputMask pIn z)

def eventCurve (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def eventResidualTuple (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Residual pIn → AES.Word :=
  fun i => c.val i.val

def inputConditions (z : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i, maskBit z i = true → x i = 0

def eventResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn z) (fun c => h (eventResidualTuple pOut pIn z c))

/-- No size or MDS hypothesis is needed for this finite source transport. -/
def eventSourceEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) :
    {c : Code pOut pIn // inputConditions z c.val} ≃ EventCode pOut pIn z where
  toFun c := ⟨c.val.val, by
    constructor
    · exact c.val.property.1
    · intro i hi
      rw [eventInputMask, maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact c.val.property.2 i hi
      · exact c.property i hi⟩
  invFun c := ⟨⟨c.val, by
    constructor
    · exact c.property.1
    · intro i hi
      apply c.property.2 i
      rw [eventInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi⟩, by
    intro i hi
    apply c.property.2 i
    rw [eventInputMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inr hi⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem eventResponse_eq_subtype_sum (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    eventResponse pOut pIn z h y =
      ∑ c : {c : Code pOut pIn // inputConditions z c.val},
        h (residualTuple pOut pIn c.val) * bareKernel pOut pIn y c.val := by
  unfold eventResponse IndexedTripleEnergy.response
  exact ((eventSourceEquiv pOut pIn z).sum_comp
    (fun c : EventCode pOut pIn z =>
      h (eventResidualTuple pOut pIn z c) *
        ∏ i : Retained pOut,
          residualMatrix AES.wordSuperboxKernel 0 (y i) (eventCurve pOut pIn z c i))).symm

def conditionalResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if inputConditions z c.val then
    h (residualTuple pOut pIn c) * bareKernel pOut pIn y c else 0

theorem conditionalResponse_eq_eventResponse (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalResponse pOut pIn z h = eventResponse pOut pIn z h := by
  classical
  funext y
  rw [eventResponse_eq_subtype_sum]
  unfold conditionalResponse
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

section LabelledMasks
variable {pIn : SelectedSupport 2 4}

def singleMask (u : SourceUniformPositions pIn) : Fin 16 := singletonMask u.val.val

def doubleMask (u v : SourceUniformPositions pIn) : Fin 16 :=
  maskUnion (singleMask u) (singleMask v)

theorem uniform_labels_ne (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    u.val.val ≠ v.val.val := by
  intro he
  apply huv
  exact Subtype.ext (Subtype.ext he)

theorem singleMask_size (u : SourceUniformPositions pIn) :
    maskSize (singleMask u) = 1 := singletonMask_size u.val.val

theorem singleMask_disjoint (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    MaskDisjoint (singleMask u) (singleMask v) := by
  intro i hi hj
  apply uniform_labels_ne u v huv
  exact ((singletonMask_bit u.val.val i).mp hi).symm.trans
    ((singletonMask_bit v.val.val i).mp hj)

theorem singleMask_residual_disjoint (u : SourceUniformPositions pIn) :
    MaskDisjoint (singleMask u) pIn.val.val.1 := by
  intro i hi hr
  have he : i = u.val.val := (singletonMask_bit u.val.val i).mp hi
  subst i
  exact u.val.property hr

theorem doubleMask_size (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    maskSize (doubleMask u v) = 2 := by
  have hd : MaskDisjoint (singleMask u) (singleMask v) := by
    intro i hi hj
    apply uniform_labels_ne u v huv
    exact ((singletonMask_bit u.val.val i).mp hi).symm.trans
      ((singletonMask_bit v.val.val i).mp hj)
  rw [doubleMask, maskUnion_size _ _ hd, singleMask_size, singleMask_size]

theorem doubleMask_residual_disjoint (u v : SourceUniformPositions pIn) :
    MaskDisjoint (doubleMask u v) pIn.val.val.1 := by
  intro i hi hr
  rw [doubleMask, maskUnion_bit, Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · exact singleMask_residual_disjoint u i hi hr
  · exact singleMask_residual_disjoint v i hi hr

theorem single_conditions_iff (u : SourceUniformPositions pIn) (x : AES.WordState) :
    inputConditions (singleMask u) x ↔ x u.val.val = 0 := by
  constructor
  · intro hx
    exact hx u.val.val ((singletonMask_bit _ _).mpr rfl)
  · intro hx i hi
    rw [(singletonMask_bit u.val.val i).mp hi]
    exact hx

theorem double_conditions_iff (u v : SourceUniformPositions pIn) (x : AES.WordState) :
    inputConditions (doubleMask u v) x ↔ x u.val.val = 0 ∧ x v.val.val = 0 := by
  constructor
  · intro hx
    constructor
    · apply hx u.val.val
      rw [doubleMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl ((singletonMask_bit _ _).mpr rfl)
    · apply hx v.val.val
      rw [doubleMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inr ((singletonMask_bit _ _).mpr rfl)
  · rintro ⟨hu, hv⟩ i hi
    rw [doubleMask, maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · rw [(singletonMask_bit u.val.val i).mp hi]
      exact hu
    · rw [(singletonMask_bit v.val.val i).mp hi]
      exact hv


end LabelledMasks

/-- Both retained outputs form the actual single-zero plane's output information set. -/
def singleRetainedHom (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u : SourceUniformPositions pIn) :
    EventCode pOut pIn (singleMask u) →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 (eventInputMask pIn (singleMask u)) pOut.val.val.1

@[simp]
theorem singleRetainedHom_apply (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u : SourceUniformPositions pIn) (c : EventCode pOut pIn (singleMask u))
    (i : Retained pOut) :
    singleRetainedHom pOut pIn u c i = eventCurve pOut pIn (singleMask u) c i := rfl

theorem single_retained_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn) :
    Function.Bijective (singleRetainedHom pOut pIn u) := by
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pOut.val.val.1 = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, singleMask_size, retainedMask_size]
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pOut.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

def singleRetainedEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u : SourceUniformPositions pIn) :
    EventCode pOut pIn (singleMask u) ≃ (Retained pOut → AES.Word) :=
  Equiv.ofBijective _ (single_retained_bijective pOut pIn u)

/-- The whole original residual pair parametrizes the singleton event plane. -/
theorem single_residual_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn) :
    Function.Bijective (eventResidualTuple pOut pIn (singleMask u)) := by
  have hz : MaskDisjoint (eventInputMask pIn (singleMask u)) pIn.val.val.1 := by
    rw [eventInputMask_eq]
    exact singleMask_residual_disjoint u
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, singleMask_size, residualMask_size]
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem single_amplitude_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (singleMask u),
      h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) = ∑ x, h x ^ 2 :=
  (Equiv.ofBijective _ (single_residual_bijective pOut pIn u)).sum_comp
    (fun x => h x ^ 2)

theorem double_retained_coordinate_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (s : Retained pOut) :
    Function.Bijective (fun c : EventCode pOut pIn (doubleMask u v) =>
      eventCurve pOut pIn (doubleMask u v) c s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hj
    have he : i = s.val := (singletonMask_bit s.val i).mp hj
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (doubleMask u v)) +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, doubleMask_size u v huv, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)


/-- Either original residual label is a line coordinate. Keeping the complete
joint residual tuple therefore gives an injection, not a bijection onto pairs. -/
theorem double_residual_coordinate_bijective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (j : Residual pIn) :
    Function.Bijective (fun c : EventCode pOut pIn (doubleMask u v) => c.val j.val) := by
  have hz : MaskDisjoint (eventInputMask pIn (doubleMask u v)) (singletonMask j.val) := by
    rw [eventInputMask_eq]
    intro i hi hj
    have hij : i = j.val := (singletonMask_bit j.val i).mp hj
    subst i
    exact doubleMask_residual_disjoint u v j.val hi j.property
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (doubleMask u v)) +
      maskSize (singletonMask j.val) = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, doubleMask_size u v huv, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) j.val).bijective.comp
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem double_residual_injective (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    Function.Injective (eventResidualTuple pOut pIn (doubleMask u v)) := by
  haveI : Nonempty (Residual pIn) :=
    Fintype.card_pos_iff.mp (by rw [residualCoordinates_card]; norm_num)
  let j : Residual pIn := Classical.choice inferInstance
  intro c d hcd
  exact (double_residual_coordinate_bijective pOut pIn u v huv j).1 (congrFun hcd j)

theorem double_amplitude_energy_le (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) ≤ ∑ x, h x ^ 2 :=
  IndexedTripleEnergy.restriction_energy_le _
    (double_residual_injective pOut pIn u v huv) h

def freeTupleEquiv (pOut : SelectedSupport 2 3) (s : Retained pOut) :
    (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) ≃ AES.Word where
  toFun w := w ⟨s, rfl⟩
  invFun v := fun _ => v
  left_inv w := by
    funext i
    have hi : i = ⟨s, rfl⟩ := Subtype.ext i.property
    rw [hi]
  right_inv _ := rfl

def doubleRetainedFreeEquiv (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (s : Retained pOut) :
    EventCode pOut pIn (doubleMask u v) ≃
      (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (Equiv.ofBijective _ (double_retained_coordinate_bijective pOut pIn u v huv s)).trans
    (freeTupleEquiv pOut s).symm

theorem doubleRetainedFreeEquiv_apply (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (s : Retained pOut) (c : EventCode pOut pIn (doubleMask u v))
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    doubleRetainedFreeEquiv pOut pIn u v huv s c i =
      eventCurve pOut pIn (doubleMask u v) c i.val := by
  change eventCurve pOut pIn (doubleMask u v) c s =
    eventCurve pOut pIn (doubleMask u v) c i.val
  rw [i.property]

theorem line_freeCoordinates_card (pOut : SelectedSupport 2 3) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  simp only [FreeCoordinates, Fintype.card_subtype_eq]

theorem line_dependentCoordinates_card (pOut : SelectedSupport 2 3) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  change Fintype.card {i : Retained pOut // ¬ i = s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

/-- This transport changes no state, residual pair, label or amplitude value. -/
theorem single_zeroResponse_eq (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    OmittedUniformTwoInputPairSource.zeroResponse pOut pIn u h =
      eventResponse pOut pIn (singleMask u) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold OmittedUniformTwoInputPairSource.zeroResponse
    WeightedResponse.zeroResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [single_conditions_iff]
  by_cases hz : c.val u.val.val = 0 <;> simp [hz]

theorem double_intersectionResponse_eq (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    OmittedUniformTwoInputPairSource.intersectionResponse pOut pIn u v h =
      eventResponse pOut pIn (doubleMask u v) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold OmittedUniformTwoInputPairSource.intersectionResponse
    TripleResponse.intersectionResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [double_conditions_iff]
  by_cases hz : c.val u.val.val = 0 ∧ c.val v.val.val = 0 <;> simp [hz]

end AESConcrete.OmittedUniformPairEventGeometry
