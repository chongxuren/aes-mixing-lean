import AESConcrete.WeightedThreeOutputGeometry
import AESConcrete.TripleResponse

/-!
# Physical input-zero geometry and exact source transport

The first shortened-code mask constrains OUTPUTS and the second INPUTS.
Singleton input-zero planes project bijectively to retained and residual
pairs. The double-zero line projects bijectively to any retained or residual
singleton; its residual-pair map is injective, so its amplitude has subenergy
only. Exact conditional sums remain on the original base Code and actual
physical uniform labels. The companion EventEnergy module supplies response
bounds.

Fixed constructive AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

The full-code Geometry and FullEnergy modules are not premises.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoUniformThreeOutputEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry
  (Code Retained Residual SourceUniformPositions curve residualTuple
    retainedMask_size residualMask_size outputInactiveMask_size
    retainedCoordinates_card)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000

-- User scope: keep the two actual uniform labels; do not pick new coordinates.
-- Keep finite decide proofs above the classical predicate instance.
theorem inputInactiveMask_eq_zero :
    ∀ pIn : SelectedSupport 2 4, pIn.val.val.2 = 0 := by decide

theorem maskUnion_zero_left : ∀ z : Fin 16, maskUnion 0 z = z := by decide

attribute [local instance] Classical.propDecidable

def eventInputMask (pIn : SelectedSupport 2 4) (z : Fin 16) : Fin 16 :=
  maskUnion pIn.val.val.2 z

theorem eventInputMask_eq (pIn : SelectedSupport 2 4) (z : Fin 16) :
    eventInputMask pIn z = z := by
  simpa only [eventInputMask, inputInactiveMask_eq_zero] using maskUnion_zero_left z

abbrev EventCode (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (eventInputMask pIn z)

def eventCurve (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def eventResidualTuple (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Residual pIn → AES.Word :=
  fun i => c.val i.val

def inputConditions (z : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i, maskBit z i = true → x i = 0

/-- The kernel is the actual retained triple, with its original labels. -/
def baseKernel (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv c.val i.val)

def eventResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn z) (fun c => h (eventResidualTuple pOut pIn z c))

/-- No size or MDS hypothesis is needed for this finite source transport. -/
def eventSourceEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
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

theorem eventResponse_eq_subtype_sum (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    eventResponse pOut pIn z h y =
      ∑ c : {c : Code pOut pIn // inputConditions z c.val},
        h (residualTuple pOut pIn c.val) * baseKernel pOut pIn y c.val := by
  unfold eventResponse IndexedTripleEnergy.response
  exact ((eventSourceEquiv pOut pIn z).sum_comp
    (fun c : EventCode pOut pIn z =>
      h (eventResidualTuple pOut pIn z c) *
        ∏ i : Retained pOut,
          residualMatrix AES.wordSuperboxKernel 0 (y i) (eventCurve pOut pIn z c i))).symm

def conditionalResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if inputConditions z c.val then
    h (residualTuple pOut pIn c) * baseKernel pOut pIn y c else 0

theorem conditionalResponse_eq_eventResponse (pOut : SelectedSupport 3 3)
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

/-- One output zero plus one actual input zero leaves a plane. -/
theorem single_retained_pair_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn) (s : Retained pOut) :
    Function.Bijective (fun c : EventCode pOut pIn (singleMask u) =>
      fun i : {i : Retained pOut // i ≠ s} => eventCurve pOut pIn (singleMask u) c i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 s
  have hp : maskSize pair = 2 :=
    DoubleUniformGeometry.retainedPairMask_size _ (retainedMask_size pOut) s
  have hr : MaskDisjoint pOut.val.val.2 pair := by
    intro i hi hj
    exact pOut.val.property.1 i hi
      ((DoubleUniformGeometry.retainedPairMask_bit _ s i).mp hj).1
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pair = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, singleMask_size, hp]
  have hb : Function.Bijective (fun c : EventCode pOut pIn (singleMask u) =>
      fun i : MaskCoordinates pair => wordMixAddEquiv.toAddMonoidHom c.val i.val) :=
    (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ pair hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective
  exact (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := AES.Word)
    pOut.val.val.1 s).bijective.comp hb

theorem single_residual_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn) :
    Function.Bijective (eventResidualTuple pOut pIn (singleMask u)) := by
  have hz : MaskDisjoint (eventInputMask pIn (singleMask u)) pIn.val.val.1 := by
    rw [eventInputMask_eq]
    exact singleMask_residual_disjoint u
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, singleMask_size, residualMask_size]
    norm_num
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem single_amplitude_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (singleMask u),
      h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) = ∑ x, h x ^ 2 :=
  (Equiv.ofBijective _ (single_residual_bijective pOut pIn u)).sum_comp (fun x => h x ^ 2)

theorem double_retained_coordinate_bijective (pOut : SelectedSupport 3 3)
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

theorem double_residual_coordinate_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (i : Residual pIn) :
    Function.Bijective (fun c : EventCode pOut pIn (doubleMask u v) => c.val i.val) := by
  have hz : MaskDisjoint (eventInputMask pIn (doubleMask u v)) (singletonMask i.val) := by
    rw [eventInputMask_eq]
    intro j hj hi
    apply doubleMask_residual_disjoint u v j hj
    rw [(singletonMask_bit i.val j).mp hi]
    exact i.property
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (doubleMask u v)) +
      maskSize (singletonMask i.val) = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, doubleMask_size u v huv, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) i.val).bijective.comp
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem double_residual_injective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    Function.Injective (eventResidualTuple pOut pIn (doubleMask u v)) := by
  haveI : Nonempty (Residual pIn) := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (MaskCoordinates pIn.val.val.1)
    rw [maskCoordinates_card, residualMask_size]
    norm_num)
  let i : Residual pIn := Classical.choice inferInstance
  intro c d he
  exact (double_residual_coordinate_bijective pOut pIn u v huv i).1 (congrFun he i)

theorem double_amplitude_energy_le (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) ≤ ∑ x, h x ^ 2 :=
  IndexedTripleEnergy.restriction_energy_le _ (double_residual_injective pOut pIn u v huv) h

def doubleRetainedFreeEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (s : Retained pOut) :
    EventCode pOut pIn (doubleMask u v) ≃
      (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (Equiv.ofBijective _ (double_retained_coordinate_bijective pOut pIn u v huv s)).trans
    (WeightedThreeOutputGeometry.freeTupleEquiv pOut s).symm

theorem doubleRetainedFreeEquiv_apply (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (s : Retained pOut) (c : EventCode pOut pIn (doubleMask u v))
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    doubleRetainedFreeEquiv pOut pIn u v huv s c i =
      eventCurve pOut pIn (doubleMask u v) c i.val := by
  change eventCurve pOut pIn (doubleMask u v) c s =
    eventCurve pOut pIn (doubleMask u v) c i.val
  rw [i.property]

theorem single_zeroResponse_eq (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.zeroResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) =
        eventResponse pOut pIn (singleMask u) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold WeightedResponse.zeroResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [single_conditions_iff]
  by_cases hz : c.val u.val.val = 0 <;> simp [hz]

theorem double_intersectionResponse_eq (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    TripleResponse.intersectionResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) =
        eventResponse pOut pIn (doubleMask u v) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold TripleResponse.intersectionResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [double_conditions_iff]
  by_cases hz : c.val u.val.val = 0 ∧ c.val v.val.val = 0 <;> simp [hz]

end AESConcrete.TwoUniformThreeOutputEventGeometry
