import AESConcrete.TwoOmittedOutputRawGeometry
import AESConcrete.TwoOmittedOutputRawResponse
import AESConcrete.TripleResponse
import AESConcrete.InvariantSubspaceFourier

/-!
# Actual input-zero events for an omitted-uniform two-output response

Output support is (2,4), input support is (1,3). The original input zero Z is
included in every eventInputMask, never replaced. All event sums preserve one
arbitrary signed original residual-tuple amplitude, including its value at
zero. Single-zero planes have source energy q*sum h^2; double-zero lines have
exact source energy sum h^2. The single- plane residual- zero translation line
projects onto the entire singleton dependent output. The double event has
three original input zeros and remains a line; it is not removed and the zero
residual parameter is included.

Source geometry, conditional-sum transports and source energy are here; the
companion EventEnergy supplies analytic bounds. The sealed sibling
BareResponse owns bare full-response cancellation. No actual weighted-minor
cap is asserted. Constructive fixed AES10/14/16; independent retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoOmittedOutputRawInputEvents
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry
open AESConcrete.TwoOmittedOutputRawResponse (bareKernel)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)

set_option maxRecDepth 100000

attribute [local instance] Classical.propDecidable

/-- Every event retains the original inactive input mask Z. -/
def eventInputMask (pIn : SelectedSupport 1 3) (z : Fin 16) : Fin 16 :=
  maskUnion pIn.val.val.2 z

abbrev EventCode (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (z : Fin 16) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (eventInputMask pIn z)

def eventCurve (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (z : Fin 16) (c : EventCode pOut pIn z) : Retained pOut → AES.Word :=
  fun i => wordMixAddEquiv c.val i.val

def eventResidualTuple (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (z : Fin 16) (c : EventCode pOut pIn z) : Residual pIn → AES.Word :=
  fun i => c.val i.val

def inputConditions (z : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i, maskBit z i = true → x i = 0

def eventResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn z) (fun c => h (eventResidualTuple pOut pIn z c))

/-- No size or MDS hypothesis is needed for this finite source transport. -/
def eventSourceEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
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

theorem eventResponse_eq_subtype_sum (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (z : Fin 16)
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

def conditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : Code pOut pIn, if inputConditions z c.val then
    h (residualTuple pOut pIn c) * bareKernel pOut pIn y c else 0

theorem conditionalResponse_eq_eventResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) :
    conditionalResponse pOut pIn z h = eventResponse pOut pIn z h := by
  classical
  funext y
  rw [eventResponse_eq_subtype_sum]
  unfold conditionalResponse
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

section LabelledMasks
variable {pIn : SelectedSupport 1 3}

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

/-- Original uniform labels lie outside Z, separately from lying outside J. -/
theorem inactive_singleMask_disjoint {pIn : SelectedSupport 1 3}
    (u : SourceUniformPositions pIn) : MaskDisjoint pIn.val.val.2 (singleMask u) := by
  intro i hz hu
  have he : i = u.val.val := (singletonMask_bit _ _).mp hu
  subst i
  exact u.property hz

theorem inactive_doubleMask_disjoint {pIn : SelectedSupport 1 3}
    (u v : SourceUniformPositions pIn) : MaskDisjoint pIn.val.val.2 (doubleMask u v) := by
  intro i hz hi
  rw [doubleMask, maskUnion_bit, Bool.or_eq_true] at hi
  rcases hi with hu | hv
  · exact inactive_singleMask_disjoint u i hz hu
  · exact inactive_singleMask_disjoint v i hz hv

theorem eventInputMask_residual_disjoint (pIn : SelectedSupport 1 3) (z : Fin 16)
    (hz : MaskDisjoint z pIn.val.val.1) :
    MaskDisjoint (eventInputMask pIn z) pIn.val.val.1 := by
  intro i hi hr
  rw [eventInputMask, maskUnion_bit, Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · exact pIn.val.property.1 i hi hr
  · exact hz i hi hr

theorem single_eventInputMask_size (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) : maskSize (eventInputMask pIn (singleMask u)) = 2 := by
  rw [eventInputMask, maskUnion_size _ _ (inactive_singleMask_disjoint u),
    inputInactiveMask_size, singleMask_size]

theorem double_eventInputMask_size (pIn : SelectedSupport 1 3)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    maskSize (eventInputMask pIn (doubleMask u v)) = 3 := by
  rw [eventInputMask, maskUnion_size _ _ (inactive_doubleMask_disjoint u v),
    inputInactiveMask_size, doubleMask_size u v huv]

/-- Both retained outputs form the actual single-zero plane's output information set. -/
def singleRetainedHom (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) :
    EventCode pOut pIn (singleMask u) →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom
    pOut.val.val.2 (eventInputMask pIn (singleMask u)) pOut.val.val.1

@[simp]
theorem singleRetainedHom_apply (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) (c : EventCode pOut pIn (singleMask u))
    (i : Retained pOut) :
    singleRetainedHom pOut pIn u c i = eventCurve pOut pIn (singleMask u) c i := rfl

theorem single_retained_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn) :
    Function.Bijective (singleRetainedHom pOut pIn u) := by
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pOut.val.val.1 = 4 := by
    rw [outputInactiveMask_size, single_eventInputMask_size, retainedMask_size]
  exact (RestrictedMDSCoordinates.output_projection_bijective
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _
    pOut.val.property.1 hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

def singleResidualZeroMask {pIn : SelectedSupport 1 3}
    (u : SourceUniformPositions pIn) : Fin 16 :=
  maskUnion pIn.val.val.1 (eventInputMask pIn (singleMask u))

theorem singleResidualZeroMask_size {pIn : SelectedSupport 1 3}
    (u : SourceUniformPositions pIn) : maskSize (singleResidualZeroMask u) = 3 := by
  have hd : MaskDisjoint pIn.val.val.1 (eventInputMask pIn (singleMask u)) := by
    intro i hr hu
    exact eventInputMask_residual_disjoint pIn _ (singleMask_residual_disjoint u) i hu hr
  rw [singleResidualZeroMask, maskUnion_size _ _ hd, residualMask_size,
    single_eventInputMask_size]

abbrev SingleResidualZero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 (singleResidualZeroMask u)

def singleTranslation (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) :
    SingleResidualZero pOut pIn u →+ EventCode pOut pIn (singleMask u) where
  toFun t := ⟨t.val, t.property.1, by
    intro i hi
    apply t.property.2 i
    rw [singleResidualZeroMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inr hi⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

theorem single_amplitude_translation (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ)
    (c : EventCode pOut pIn (singleMask u)) (t : SingleResidualZero pOut pIn u) :
    h (eventResidualTuple pOut pIn (singleMask u) (c + singleTranslation pOut pIn u t)) =
      h (eventResidualTuple pOut pIn (singleMask u) c) := by
  apply congrArg h
  funext i
  change c.val i.val + t.val i.val = c.val i.val
  have hz : t.val i.val = 0 := by
    apply t.property.2 i.val
    rw [singleResidualZeroMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inl i.property
  rw [hz, add_zero]

/-- Zero output zeros, three input zeros and one retained output label total four. -/
theorem single_translation_coordinate_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn) (s : Retained pOut) :
    Function.Bijective (fun t : SingleResidualZero pOut pIn u =>
      singleRetainedHom pOut pIn u (singleTranslation pOut pIn u t) s) := by
  have hr : MaskDisjoint pOut.val.val.2 (singletonMask s.val) := by
    intro i hi hs
    have he : i = s.val := (singletonMask_bit s.val i).mp hs
    subst i
    exact pOut.val.property.1 s.val hi s.property
  have hs : maskSize pOut.val.val.2 + maskSize (singleResidualZeroMask u) +
      maskSize (singletonMask s.val) = 4 := by
    rw [outputInactiveMask_size, singleResidualZeroMask_size, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective
      wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS _ _ _ hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

theorem single_translation_dependent_surjective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn) (s : Retained pOut) :
    Function.Surjective (fun t : SingleResidualZero pOut pIn u =>
      fun i : DependentCoordinates (fun i : Retained pOut => i ≠ s) =>
        singleRetainedHom pOut pIn u (singleTranslation pOut pIn u t) i.val) :=
  InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
    (fun t : SingleResidualZero pOut pIn u =>
      singleRetainedHom pOut pIn u (singleTranslation pOut pIn u t))
    (single_translation_coordinate_bijective pOut pIn u s).2

theorem freeCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 := by
  change Fintype.card {i : Retained pOut // i ≠ s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem dependentCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
  IndexedFourierSupport.dependentCoordinates_card s

/-- The original residual tuple and another original uniform input form an
actual INPUT information set on a single-zero plane. -/
def single_residualUniformEquiv (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    EventCode pOut pIn (singleMask u) ≃ (Residual pIn → AES.Word) × AES.Word := by
  have hsu : MaskDisjoint pIn.val.val.1 (singletonMask v.val.val) := by
    intro i hi hv
    have he : i = v.val.val := (singletonMask_bit _ _).mp hv
    subst i
    exact v.val.property hi
  have hzu : MaskDisjoint (eventInputMask pIn (singleMask u))
      (maskUnion pIn.val.val.1 (singletonMask v.val.val)) := by
    intro i hi hrest
    rw [eventInputMask, maskUnion_bit, Bool.or_eq_true] at hi
    rw [maskUnion_bit, Bool.or_eq_true] at hrest
    rcases hi with hi | hi
    · rcases hrest with hr | hv
      · exact pIn.val.property.1 i hi hr
      · exact inactive_singleMask_disjoint v i hi hv
    · rcases hrest with hr | hv
      · exact singleMask_residual_disjoint u i hi hr
      · exact singleMask_disjoint u v huv i hi hv
  have hsize : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (singleMask u)) +
      maskSize pIn.val.val.1 + maskSize (singletonMask v.val.val) = 4 := by
    rw [outputInactiveMask_size, single_eventInputMask_size,
      residualMask_size, singletonMask_size]
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.inputSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ _ hsu hzu hsize)).trans
        (Equiv.prodCongr (Equiv.refl _) (singletonTupleEquiv v.val.val))

@[simp]
theorem single_residualUniformEquiv_fst (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (c : EventCode pOut pIn (singleMask u)) :
    (single_residualUniformEquiv pOut pIn u v huv c).1 =
      eventResidualTuple pOut pIn (singleMask u) c := rfl

@[simp]
theorem single_residualUniformEquiv_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (c : EventCode pOut pIn (singleMask u)) :
    (single_residualUniformEquiv pOut pIn u v huv c).2 = c.val v.val.val := rfl

/-- Each original residual tuple has exactly q points in this plane. -/
theorem single_amplitude_energy_at (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
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

theorem single_amplitude_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn)
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

theorem double_retained_coordinate_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
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
    rw [outputInactiveMask_size, double_eventInputMask_size pIn u v huv, singletonMask_size]
  exact (singletonTupleEquiv (V := AES.Word) s.val).bijective.comp
    ((RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS _ _ _ hr hs).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

/-- Zero output zeros, three input zeros and the original residual singleton
form the exact line information set. The value zero is included. -/
theorem double_residual_bijective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v) :
    Function.Bijective (eventResidualTuple pOut pIn (doubleMask u v)) := by
  have hz : MaskDisjoint (eventInputMask pIn (doubleMask u v)) pIn.val.val.1 := by
    exact eventInputMask_residual_disjoint pIn _ (doubleMask_residual_disjoint u v)
  have hs : maskSize pOut.val.val.2 + maskSize (eventInputMask pIn (doubleMask u v)) +
      maskSize pIn.val.val.1 = 4 := by
    rw [outputInactiveMask_size, double_eventInputMask_size pIn u v huv, residualMask_size]
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS _ _ _ hz hs).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective

theorem double_amplitude_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) = ∑ x, h x ^ 2 :=
  (Equiv.ofBijective _ (double_residual_bijective pOut pIn u v huv)).sum_comp
    (fun x => h x ^ 2)

theorem double_amplitude_energy_le (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : EventCode pOut pIn (doubleMask u v),
      h (eventResidualTuple pOut pIn (doubleMask u v) c) ^ 2) ≤ ∑ x, h x ^ 2 :=
  (double_amplitude_energy pOut pIn u v huv h).le

def freeTupleEquiv (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) ≃ AES.Word where
  toFun w := w ⟨s, rfl⟩
  invFun v := fun _ => v
  left_inv w := by
    funext i
    have hi : i = ⟨s, rfl⟩ := Subtype.ext i.property
    rw [hi]
  right_inv _ := rfl

def doubleRetainedFreeEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v) (s : Retained pOut) :
    EventCode pOut pIn (doubleMask u v) ≃
      (FreeCoordinates (fun i : Retained pOut => i = s) → AES.Word) :=
  (Equiv.ofBijective _ (double_retained_coordinate_bijective pOut pIn u v huv s)).trans
    (freeTupleEquiv pOut s).symm

theorem doubleRetainedFreeEquiv_apply (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (s : Retained pOut) (c : EventCode pOut pIn (doubleMask u v))
    (i : FreeCoordinates (fun i : Retained pOut => i = s)) :
    doubleRetainedFreeEquiv pOut pIn u v huv s c i =
      eventCurve pOut pIn (doubleMask u v) c i.val := by
  change eventCurve pOut pIn (doubleMask u v) c s =
    eventCurve pOut pIn (doubleMask u v) c i.val
  rw [i.property]

theorem line_freeCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  simp only [FreeCoordinates, Fintype.card_subtype_eq]

theorem line_dependentCoordinates_card (pOut : SelectedSupport 2 4) (s : Retained pOut) :
    Fintype.card (DependentCoordinates (fun i : Retained pOut => i = s)) = 1 := by
  change Fintype.card {i : Retained pOut // ¬ i = s} = 1
  rw [Fintype.card_subtype_compl (fun i : Retained pOut => i = s),
    Fintype.card_subtype_eq, retainedCoordinates_card]

theorem single_zeroResponse_eq (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.zeroResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) =
        eventResponse pOut pIn (singleMask u) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold WeightedResponse.zeroResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [single_conditions_iff]
  by_cases hz : c.val u.val.val = 0 <;> simp [hz]

theorem double_intersectionResponse_eq (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 3) (u v : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    TripleResponse.intersectionResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) =
        eventResponse pOut pIn (doubleMask u v) h := by
  rw [← conditionalResponse_eq_eventResponse]
  funext y
  unfold TripleResponse.intersectionResponse conditionalResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [double_conditions_iff]
  by_cases hz : c.val u.val.val = 0 ∧ c.val v.val.val = 0 <;> simp [hz]

end AESConcrete.TwoOmittedOutputRawInputEvents
