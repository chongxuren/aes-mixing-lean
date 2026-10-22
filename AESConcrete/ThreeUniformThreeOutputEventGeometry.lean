import AESConcrete.WeightedThreeOutputGeometry
import AESConcrete.TripleResponse

/-!
# Three original input-zero events on a three-output shortened code

Lemmas for (11,7). The first shortened-code mask constrains OUTPUTS and the
second INPUTS. A single original uniform-input zero leaves a plane, with
exactly q points per original residual-singleton tuple. Two distinct zeros
leave a line parametrized by that same tuple. Three distinct zeros plus the
actual output zero force the physical source to zero. No amplitude premise is
used.

Only providers are imported. New full-code Geometry and FullEnergy are
separate components. The same arbitrary signed residual-tuple h, including
h(0), is preserved by every exact source transport and counting identity.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeUniformThreeOutputEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry
  (Code Retained Residual SourceUniformPositions curve residualTuple
    retainedMask_size residualMask_size outputInactiveMask_size
    retainedCoordinates_card sourceUniformPositions_card)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000

-- User scope: keep all three actual uniform labels and arbitrary h(0).
-- Keep finite decide proofs above the classical predicate instance.
theorem inputInactiveMask_eq_zero :
    ∀ pIn : SelectedSupport 1 4, pIn.val.val.2 = 0 := by decide

theorem maskUnion_zero_left : ∀ z : Fin 16, maskUnion 0 z = z := by decide

attribute [local instance] Classical.propDecidable

def eventInputMask (pIn : SelectedSupport 1 4) (z : Fin 16) : Fin 16 :=
  maskUnion pIn.val.val.2 z

theorem eventInputMask_eq (pIn : SelectedSupport 1 4) (z : Fin 16) :
    eventInputMask pIn z = z := by
  simpa only [eventInputMask, inputInactiveMask_eq_zero] using maskUnion_zero_left z

abbrev EventCode (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (z : Fin 16) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (eventInputMask pIn z)

def eventCurve (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def eventResidualTuple (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (z : Fin 16) (c : EventCode pOut pIn z) : Residual pIn → AES.Word :=
  fun i => c.val i.val

def inputConditions (z : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i, maskBit z i = true → x i = 0

/-- The kernel is the actual retained triple, with its original labels. -/
def baseKernel (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv c.val i.val)

def eventResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn z) (fun c => h (eventResidualTuple pOut pIn z c))

/-- No size or MDS hypothesis is needed for this finite source transport. -/
def eventSourceEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
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
    (pIn : SelectedSupport 1 4) (z : Fin 16)
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

def conditionalResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if inputConditions z c.val then
    h (residualTuple pOut pIn c) * baseKernel pOut pIn y c else 0

theorem conditionalResponse_eq_eventResponse (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalResponse pOut pIn z h = eventResponse pOut pIn z h := by
  classical
  funext y
  rw [eventResponse_eq_subtype_sum]
  unfold conditionalResponse
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

section LabelledMasks
variable {pIn : SelectedSupport 1 4}

def singleMask (u : SourceUniformPositions pIn) : Fin 16 := singletonMask u.val.val

def doubleMask (u v : SourceUniformPositions pIn) : Fin 16 :=
  maskUnion (singleMask u) (singleMask v)

def tripleMask (u v w : SourceUniformPositions pIn) : Fin 16 :=
  maskUnion (doubleMask u v) (singleMask w)

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

theorem tripleMask_size (u v w : SourceUniformPositions pIn)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    maskSize (tripleMask u v w) = 3 := by
  have hd : MaskDisjoint (doubleMask u v) (singleMask w) := by
    intro i hi hw
    rw [doubleMask, maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact singleMask_disjoint u w huw i hi hw
    · exact singleMask_disjoint v w hvw i hi hw
  rw [tripleMask, maskUnion_size _ _ hd, doubleMask_size u v huv, singleMask_size]

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

theorem triple_conditions_iff (u v w : SourceUniformPositions pIn) (x : AES.WordState) :
    inputConditions (tripleMask u v w) x ↔
      x u.val.val = 0 ∧ x v.val.val = 0 ∧ x w.val.val = 0 := by
  constructor
  · intro hx
    have huv : inputConditions (doubleMask u v) x := by
      intro i hi
      apply hx i
      rw [tripleMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi
    have hw : inputConditions (singleMask w) x := by
      intro i hi
      apply hx i
      rw [tripleMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inr hi
    exact ⟨((double_conditions_iff u v x).mp huv).1,
      ((double_conditions_iff u v x).mp huv).2, (single_conditions_iff w x).mp hw⟩
  · rintro ⟨hu, hv, hw⟩ i hi
    rw [tripleMask, maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact (double_conditions_iff u v x).mpr ⟨hu, hv⟩ i hi
    · exact (single_conditions_iff w x).mpr hw i hi

end LabelledMasks

/-- One output zero plus one actual input zero leaves a plane. -/
theorem single_retained_pair_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn) (s : Retained pOut) :
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

/-- The original residual tuple and another original uniform input form an
actual INPUT information set on a single-zero plane. -/
def single_residualUniformEquiv (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    EventCode pOut pIn (singleMask u) ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hsu : MaskDisjoint pIn.val.val.1 (singletonMask v.val.val) := by
    intro i hi hv
    have he : i = v.val.val := (singletonMask_bit _ _).mp hv
    subst i
    exact v.val.property hi
  have hzu : MaskDisjoint (eventInputMask pIn (singleMask u))
      (maskUnion pIn.val.val.1 (singletonMask v.val.val)) := by
    rw [eventInputMask_eq]
    intro i hi hrest
    rw [maskUnion_bit, Bool.or_eq_true] at hrest
    rcases hrest with hr | hv
    · exact singleMask_residual_disjoint u i hi hr
    · exact singleMask_disjoint u v huv i hi hv
  have hsize : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pIn.val.val.1 + maskSize (singletonMask v.val.val) = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, singleMask_size,
      residualMask_size, singletonMask_size]
    norm_num
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hsu hzu hsize)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv v.val.val))

@[simp]
theorem single_residualUniformEquiv_fst (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (c : EventCode pOut pIn (singleMask u)) :
    (single_residualUniformEquiv pOut pIn u v huv c).1 =
      eventResidualTuple pOut pIn (singleMask u) c := rfl

@[simp]
theorem single_residualUniformEquiv_snd (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (c : EventCode pOut pIn (singleMask u)) :
    (single_residualUniformEquiv pOut pIn u v huv c).2 = c.val v.val.val := rfl

/-- Each original residual tuple has exactly q points in this plane. -/
theorem single_amplitude_energy_at (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (singleMask u),
      h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ x, h x ^ 2 := by
  have he := (single_residualUniformEquiv pOut pIn u v huv).sum_comp
    (fun p : (Residual pIn → AES.Word) × AES.Word => h p.1 ^ 2)
  change (∑ c : EventCode pOut pIn (singleMask u),
    h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) =
      ∑ p : (Residual pIn → AES.Word) × AES.Word, h p.1 ^ 2 at he
  rw [he, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem single_amplitude_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (singleMask u),
      h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) =
      (Fintype.card AES.Word : ℝ) * ∑ x, h x ^ 2 := by
  haveI : Nonempty {v : SourceUniformPositions pIn // v ≠ u} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_subtype_compl (fun v : SourceUniformPositions pIn => v = u),
        Fintype.card_subtype_eq, sourceUniformPositions_card]
      norm_num)
  let v : {v : SourceUniformPositions pIn // v ≠ u} := Classical.choice inferInstance
  exact single_amplitude_energy_at pOut pIn u v.val v.property.symm h

theorem double_retained_coordinate_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
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

/-- One output zero, two input zeros and the original residual singleton
form the exact line information set. The value zero is included. -/
theorem double_residual_bijective (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    Function.Bijective (eventResidualTuple pOut pIn (doubleMask u v)) := by
  have hz : MaskDisjoint (eventInputMask pIn (doubleMask u v)) pIn.val.val.1 := by
    rw [eventInputMask_eq]
    exact doubleMask_residual_disjoint u v
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (doubleMask u v)) +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, eventInputMask_eq, doubleMask_size u v huv, residualMask_size]
    norm_num
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem double_amplitude_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) = ∑ x, h x ^ 2 :=
  (Equiv.ofBijective _ (double_residual_bijective pOut pIn u v huv)).sum_comp
    (fun x => h x ^ 2)

theorem double_amplitude_energy_le (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) ≤ ∑ x, h x ^ 2 :=
  (double_amplitude_energy pOut pIn u v huv h).le

def doubleRetainedFreeEquiv (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (s : Retained pOut) :
    EventCode pOut pIn (doubleMask u v) ≃
      (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (Equiv.ofBijective _ (double_retained_coordinate_bijective pOut pIn u v huv s)).trans
    (WeightedThreeOutputGeometry.freeTupleEquiv pOut s).symm

theorem doubleRetainedFreeEquiv_apply (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (s : Retained pOut) (c : EventCode pOut pIn (doubleMask u v))
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    doubleRetainedFreeEquiv pOut pIn u v huv s c i =
      eventCurve pOut pIn (doubleMask u v) c i.val := by
  change eventCurve pOut pIn (doubleMask u v) c s =
    eventCurve pOut pIn (doubleMask u v) c i.val
  rw [i.property]

theorem single_zeroResponse_eq (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
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
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn)
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

/-- Four actual MDS zero conditions kill the source, without any h(0) premise. -/
theorem triple_zero_source (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (c : Code pOut pIn)
    (hu : c.val u.val.val = 0) (hv : c.val v.val.val = 0) (hw : c.val w.val.val = 0) :
    c.val = 0 := by
  have hhigh : 4 ≤ maskSize pOut.val.val.2 + maskSize (tripleMask u v w) := by
    norm_num only [outputInactiveMask_size, tripleMask_size u v w huv huw hvw]
  have hz : graphZeroConditions wordMixAddEquiv.toAddMonoidHom
      pOut.val.val.2 (tripleMask u v w) c.val :=
    ⟨c.property.1, (triple_conditions_iff u v w c.val).mpr ⟨hu, hv, hw⟩⟩
  exact mds_graph_zero_high wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
    pOut.val.val.2 (tripleMask u v w) hhigh c.val hz

end AESConcrete.ThreeUniformThreeOutputEventGeometry
