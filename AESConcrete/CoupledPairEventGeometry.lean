import AESConcrete.CoupledPairSource
import AESConcrete.ShortenedJointGeometry
import AESConcrete.RetainedGraphMasks
import AESConcrete.ActivityCodeScalar
import AESMixing.IncidenceCounting

/-!
# Actual zero-event geometry for the joint residual pair

The physical events are precisely the two ORIGINAL uniform input zeros and the
one omitted output zero. The amplitude is one arbitrary signed joint function
on the two residual input labels.

All nonempty subsets have an injective retained-triple map. Mixed residual
energy identities are restricted explicitly to event sizes at most two. The
full three-event intersection is a line: its residual-pair restriction is
injective and its amplitude energy is bounded by, not equated to, the full
joint energy. No endpoint vanishing or product-amplitude premise is used.
Fourier/ordinary response energy and physical aggregation remain separate.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairFiber
  (ResidualPositions RetainedPositions omittedLabel omitted_not_retained
    inactiveLabel_not residualMask_size)
open AESConcrete.CoupledPairSource
  (SourceUniformPositions SourceWord source source_uniform source_residual sourceWordEquiv)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv retainedHom)
open AESConcrete.ShortenedJointGeometry (Translation translation)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

attribute [local instance] Classical.propDecidable

private theorem zeroMask_not (i : Fin 4) : maskBit (0 : Fin 16) i ≠ true := by
  intro hi
  exact (empty_mask_coordinate ⟨i, hi⟩).elim

private theorem zeroMask_disjoint (m : Fin 16) : MaskDisjoint 0 m := by
  intro i hi
  exact (zeroMask_not i hi).elim

private theorem wordMixHom_apply (x : AES.WordState) :
    wordMixAddEquiv.toAddMonoidHom x = wordMixAddEquiv x := rfl

/-- The omitted output and the two original uniform input positions. -/
def eventPositions (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Finset GraphPosition :=
  unmarkedGraphPositions 0 0 pOut.val.val.1 pIn.val.val.1

theorem eventPositions_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    (eventPositions pOut pIn).card = 3 := by
  rw [eventPositions, unmarkedGraphPositions_card 0 0 _ _
    (zeroMask_disjoint _) (zeroMask_disjoint _),
    ThreeActiveGeometry.retainedMask_size, residualMask_size]
  rw [show maskSize (0 : Fin 16) = 0 by decide]

theorem eventPositions_output (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (i : Fin 4) : Sum.inl i ∈ eventPositions pOut pIn ↔ i = omittedLabel pOut := by
  rw [eventPositions, unmarkedGraphPositions_output]
  constructor
  · intro hi
    exact CoupledPairFiber.nonretained_eq_omitted pOut i hi.2
  · intro hi
    subst i
    exact ⟨zeroMask_not _, omitted_not_retained pOut⟩

theorem eventPositions_input (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (i : Fin 4) :
    Sum.inr i ∈ eventPositions pOut pIn ↔ maskBit pIn.val.val.1 i ≠ true := by
  rw [eventPositions, unmarkedGraphPositions_input]
  constructor
  · exact fun hi => hi.2
  · exact fun hi => ⟨zeroMask_not _, hi⟩

theorem eventPositions_input_uniform
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) (i : Fin 4) :
    Sum.inr i ∈ eventPositions pOut pIn ↔
      ∃ j : SourceUniformPositions pIn, j.val.val = i := by
  rw [eventPositions_input]
  constructor
  · intro hi
    exact ⟨⟨⟨i, hi⟩, inactiveLabel_not pIn i⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact j.val.property

def eventsOfSize (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) (m : ℕ) :
    Finset (Finset GraphPosition) := (eventPositions pOut pIn).powersetCard m

theorem eventsOfSize_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) (m : ℕ) :
    (eventsOfSize pOut pIn m).card = Nat.choose 3 m := by
  rw [eventsOfSize, Finset.card_powersetCard, eventPositions_card]

theorem nonempty_family_sizes (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    (eventsOfSize pOut pIn 1).card = 3 ∧ (eventsOfSize pOut pIn 2).card = 3 ∧
      (eventsOfSize pOut pIn 3).card = 1 := by
  simp only [eventsOfSize_card]
  norm_num [Nat.choose]

/-- The triple endpoint is included, with separate geometry below. -/
abbrev Events (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :=
  {s : Finset GraphPosition // s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 3}

theorem events_of_mem (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ 3) (s : Finset GraphPosition)
    (hs : s ∈ eventsOfSize pOut pIn m) :
    s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 3 := by
  have hh := Finset.mem_powersetCard.mp hs
  exact ⟨hh.1, by omega, by omega⟩

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) : AES.Word :=
  wordMixAddEquiv (sourceWordEquiv pIn uv) (omittedLabel pOut)

def retainedMap (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) : RetainedPositions pOut → AES.Word :=
  fun i => wordMixAddEquiv (sourceWordEquiv pIn uv) i.val

section Nonempty
variable {pOut : SelectedSupport 3 4} {pIn : SelectedSupport 2 4}

def outputZeroMask (s : Events pOut pIn) : Fin 16 := outputPositionMask s.val
def inputZeroMask (s : Events pOut pIn) : Fin 16 := inputPositionMask s.val

theorem constraint_count (s : Events pOut pIn) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) = s.val.card :=
  selected_position_count s.val

theorem outputZeros_disjoint_retained (s : Events pOut pIn) :
    MaskDisjoint (outputZeroMask s) pOut.val.val.1 := by
  intro i hi hout
  have he := (eventPositions_output pOut pIn i).mp
    (s.property.1 ((outputPositionMask_bit s.val i).mp hi))
  exact omitted_not_retained pOut (he ▸ hout)

theorem inputZeros_disjoint_residual (s : Events pOut pIn) :
    MaskDisjoint (inputZeroMask s) pIn.val.val.1 := by
  intro i hi hE
  have he := (eventPositions_input pOut pIn i).mp
    (s.property.1 ((inputPositionMask_bit s.val i).mp hi))
  exact he hE

def informationCount (s : Events pOut pIn) : Fin 5 :=
  ⟨4 - s.val.card, by have hlo := s.property.2.1; omega⟩

theorem informationCount_le (s : Events pOut pIn) : informationCount s ≤ 3 := by
  change 4 - s.val.card ≤ (3 : ℕ)
  have hlo := s.property.2.1
  omega

def informationMask (s : Events pOut pIn) : Fin 16 :=
  RetainedGraphMasks.freeMask 3 (informationCount s) (informationCount_le s) pOut

theorem informationMask_spec (s : Events pOut pIn) :
    maskSize (informationMask s) = 4 - s.val.card ∧
      RetainedGraphMasks.Submask (informationMask s) pOut.val.val.1 :=
  RetainedGraphMasks.freeMask_spec 3 (informationCount s) (informationCount_le s) pOut

theorem informationMask_disjoint (s : Events pOut pIn) :
    MaskDisjoint (outputZeroMask s) (informationMask s) := by
  intro i hi hinfo
  exact outputZeros_disjoint_retained s i hi ((informationMask_spec s).2 i hinfo)

theorem information_size_identity (s : Events pOut pIn) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) +
      maskSize (informationMask s) = 4 := by
  have hc := constraint_count s
  have hi := (informationMask_spec s).1
  have hup := s.property.2.2
  omega

/-- Exactly the selected physical zeros on a complete four-word input. -/
def eventConditions (s : Events pOut pIn) (w : AES.WordState) : Prop :=
  ∀ e ∈ s.val, graphCoordinate wordMixAddEquiv.toAddMonoidHom w e = 0

theorem eventConditions_iff (s : Events pOut pIn) (w : AES.WordState) :
    graphZeroConditions wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s) w ↔
      eventConditions s w := by
  constructor
  · intro hw e he
    cases e with
    | inl i => exact hw.1 i ((outputPositionMask_bit s.val i).mpr he)
    | inr i => exact hw.2 i ((inputPositionMask_bit s.val i).mpr he)
  · intro hw
    constructor
    · intro i hi
      exact hw (Sum.inl i) ((outputPositionMask_bit s.val i).mp hi)
    · intro i hi
      exact hw (Sum.inr i) ((inputPositionMask_bit s.val i).mp hi)

theorem eventConditions_source_iff (s : Events pOut pIn)
    (u : ResidualPositions pIn → AES.Word) (v : SourceUniformPositions pIn → AES.Word) :
    eventConditions s (source pIn u v) ↔
      (∀ j : SourceUniformPositions pIn, Sum.inr j.val.val ∈ s.val → v j = 0) ∧
      (Sum.inl (omittedLabel pOut) ∈ s.val → omittedValue pOut pIn (u, v) = 0) := by
  constructor
  · intro hs
    constructor
    · intro j hj
      have hz := hs (Sum.inr j.val.val) hj
      change source pIn u v j.val.val = 0 at hz
      simpa only [source_uniform] using hz
    · intro hj
      have hz := hs (Sum.inl (omittedLabel pOut)) hj
      change wordMixAddEquiv.toAddMonoidHom (source pIn u v) (omittedLabel pOut) = 0 at hz
      rw [wordMixHom_apply] at hz
      exact hz
  · rintro ⟨hinput, houtput⟩ e he
    cases e with
    | inl i =>
      have hi := (eventPositions_output pOut pIn i).mp (s.property.1 he)
      subst i
      change wordMixAddEquiv.toAddMonoidHom (source pIn u v) (omittedLabel pOut) = 0
      rw [wordMixHom_apply]
      exact houtput he
    | inr i =>
      let j : SourceUniformPositions pIn :=
        ⟨⟨i, (eventPositions_input pOut pIn i).mp (s.property.1 he)⟩, inactiveLabel_not pIn i⟩
      change source pIn u v j.val.val = 0
      rw [source_uniform]
      exact hinput j he

abbrev EventCode (s : Events pOut pIn) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)

abbrev EventSource (s : Events pOut pIn) :=
  {uv : SourceWord pIn // eventConditions s (sourceWordEquiv pIn uv)}

instance eventSourceFintype (s : Events pOut pIn) : Fintype (EventSource s) := by
  classical
  exact inferInstance

/-- The actual original source restriction, with the same physical states. -/
def eventSourceEquiv (s : Events pOut pIn) : EventSource s ≃ EventCode s where
  toFun uv := ⟨sourceWordEquiv pIn uv.val, (eventConditions_iff s _).mpr uv.property⟩
  invFun c := ⟨(sourceWordEquiv pIn).symm c.val, by
    rw [Equiv.apply_symm_apply]
    exact (eventConditions_iff s c.val).mp c.property⟩
  left_inv uv := Subtype.ext ((sourceWordEquiv pIn).symm_apply_apply uv.val)
  right_inv c := Subtype.ext ((sourceWordEquiv pIn).apply_symm_apply c.val)

theorem eventCode_card (s : Events pOut pIn) :
    Fintype.card (EventCode s) = Fintype.card AES.Word ^ (4 - s.val.card) := by
  calc
    _ = Fintype.card (ShortenedGraph wordMixAddEquiv.toAddMonoidHom
        (outputZeroMask s) (inputZeroMask s)) :=
      Fintype.card_congr (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _)
    _ = _ := by
      rw [mds_graph_zero_count wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS,
        constraint_count]

theorem eventSource_card (s : Events pOut pIn) :
    Fintype.card (EventSource s) = Fintype.card AES.Word ^ (4 - s.val.card) :=
  (Fintype.card_congr (eventSourceEquiv s)).trans (eventCode_card s)

def eventRetainedHom (s : Events pOut pIn) : EventCode s →+ (RetainedPositions pOut → AES.Word) :=
  retainedHom wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s) pOut.val.val.1

def eventResidualHom (s : Events pOut pIn) : EventCode s →+ (ResidualPositions pIn → AES.Word) :=
  ShortenedJointGeometry.residualHom wordMixAddEquiv.toAddMonoidHom
    (outputZeroMask s) (inputZeroMask s) pIn.val.val.1

@[simp]
theorem eventRetainedHom_apply (s : Events pOut pIn) (c : EventCode s) (i : RetainedPositions pOut) :
    eventRetainedHom s c i = wordMixAddEquiv c.val i.val := rfl

@[simp]
theorem eventResidualHom_apply (s : Events pOut pIn) (c : EventCode s) (i : ResidualPositions pIn) :
    eventResidualHom s c i = c.val i.val := rfl

theorem eventSourceEquiv_residual (s : Events pOut pIn) (uv : EventSource s) :
    eventResidualHom s (eventSourceEquiv s uv) = uv.val.1 := by
  funext i
  exact source_residual pIn uv.val.1 uv.val.2 i

theorem eventInformationProjection_bijective (s : Events pOut pIn) :
    Function.Bijective (fun c : EventCode s =>
      fun i : MaskCoordinates (informationMask s) => wordMixAddEquiv c.val i.val) := by
  have hb := (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) (informationMask s)
    (informationMask_disjoint s) (information_size_identity s)).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective
  exact hb

theorem eventRetainedHom_injective (s : Events pOut pIn) :
    Function.Injective (eventRetainedHom s) :=
  ShortenedWeightedGeometry.retainedHom_injective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (informationMask s) (informationMask_disjoint s) (informationMask_spec s).2
    (information_size_identity s)

theorem eventSource_retained_injective (s : Events pOut pIn) :
    Function.Injective (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by
  have he : (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv)) =
      (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by rfl
  rw [← he]
  exact (eventRetainedHom_injective s).comp (eventSourceEquiv s).injective

-- This mixed family deliberately stops at m=2. At m=3, 3+|E|=5, so
-- replacing a negative dimension by truncated subtraction would be invalid.
def dependentCount (s : Events pOut pIn) (_hs : s.val.card ≤ 2) : Fin 5 :=
  ⟨2 - s.val.card, by omega⟩

theorem dependentCount_le (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    dependentCount s hs ≤ 3 := by
  change 2 - s.val.card ≤ (3 : ℕ)
  omega

def dependentMask (s : Events pOut pIn) (hs : s.val.card ≤ 2) : Fin 16 :=
  RetainedGraphMasks.freeMask 3 (dependentCount s hs) (dependentCount_le s hs) pOut

theorem dependentMask_spec (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    maskSize (dependentMask s hs) = 2 - s.val.card ∧
      RetainedGraphMasks.Submask (dependentMask s hs) pOut.val.val.1 :=
  RetainedGraphMasks.freeMask_spec 3 (dependentCount s hs) (dependentCount_le s hs) pOut

theorem dependentMask_disjoint (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    MaskDisjoint (outputZeroMask s) (dependentMask s hs) := by
  intro i hi hdep
  exact outputZeros_disjoint_retained s i hi ((dependentMask_spec s hs).2 i hdep)

theorem dependent_size_identity (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) + maskSize pIn.val.val.1 +
      maskSize (dependentMask s hs) = 4 := by
  have hc := constraint_count s
  have hd := (dependentMask_spec s hs).1
  have hE := residualMask_size pIn
  omega

def eventMixedEquiv (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    EventCode s ≃ (ResidualPositions pIn → AES.Word) ×
      (MaskCoordinates (dependentMask s hs) → AES.Word) :=
  ShortenedJointGeometry.mixedResidualEquiv wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pIn.val.val.1
    (dependentMask s hs) (dependentMask_disjoint s hs) (inputZeros_disjoint_residual s)
    (dependent_size_identity s hs)

theorem eventMixedEquiv_residual (s : Events pOut pIn) (hs : s.val.card ≤ 2) (c : EventCode s) :
    (eventMixedEquiv s hs c).1 = eventResidualHom s c := rfl

theorem word_card_real : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
  rw [AES.word_card]
  norm_num [ActivityCodeScalar.q]

theorem eventCode_amplitude_energy (s : Events pOut pIn) (hs : s.val.card ≤ 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ c : EventCode s, h (eventResidualHom s c) ^ 2) =
      ActivityCodeScalar.q ^ (2 - s.val.card) * ∑ u, h u ^ 2 := by
  have he := ShortenedJointGeometry.amplitude_energy wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pIn.val.val.1
    (dependentMask s hs) (dependentMask_disjoint s hs) (inputZeros_disjoint_residual s)
    (dependent_size_identity s hs) h
  rw [(dependentMask_spec s hs).1, word_card_real] at he
  exact he

theorem eventSource_amplitude_energy (s : Events pOut pIn) (hs : s.val.card ≤ 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) =
      ActivityCodeScalar.q ^ (2 - s.val.card) * ∑ u, h u ^ 2 := by
  have he := (eventSourceEquiv s).sum_comp
    (fun c : EventCode s => h (eventResidualHom s c) ^ 2)
  simp_rw [eventSourceEquiv_residual] at he
  exact he.trans (eventCode_amplitude_energy s hs h)

theorem single_source_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ActivityCodeScalar.q * ∑ u, h u ^ 2 := by
  simpa only [hs, show (2 : ℕ) - 1 = 1 by decide, pow_one] using
    eventSource_amplitude_energy s (by omega) h

theorem pair_source_energy (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ∑ u, h u ^ 2 := by
  simpa only [hs, Nat.sub_self, pow_zero, one_mul] using
    eventSource_amplitude_energy s (by omega) h

/-- The entire residual-zero translation family covers the named dependent
tuple jointly. For m=1 this is the required one-dimensional physical tuple. -/
theorem eventTranslation_projection_bijective (s : Events pOut pIn) (hs : s.val.card ≤ 2) :
    Function.Bijective (ShortenedJointGeometry.retainedDependentProjection
      wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
      pIn.val.val.1 (dependentMask s hs) (dependentMask_spec s hs).2) :=
  ShortenedJointGeometry.retainedDependentProjection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    pIn.val.val.1 (dependentMask s hs) (dependentMask_disjoint s hs)
    (dependentMask_spec s hs).2 (inputZeros_disjoint_residual s) (dependent_size_identity s hs)

/-- Every retained singleton can serve as the dependent physical label at m=1. -/
theorem single_translation_output_bijective (s : Events pOut pIn) (hs : s.val.card = 1)
    (i : RetainedPositions pOut) :
    Function.Bijective (fun t : Translation wordMixAddEquiv.toAddMonoidHom
        (outputZeroMask s) (inputZeroMask s) pIn.val.val.1 =>
      eventRetainedHom s (translation wordMixAddEquiv.toAddMonoidHom
        (outputZeroMask s) (inputZeroMask s) pIn.val.val.1 t) i) := by
  have hr : MaskDisjoint (outputZeroMask s) (ShortenedLineResponse.singletonMask i.val) := by
    intro j hj hsingle
    have hji := (ShortenedLineResponse.singletonMask_bit i.val j).mp hsingle
    subst j
    exact outputZeros_disjoint_retained s i.val hj i.property
  have hsize : maskSize (outputZeroMask s) + maskSize (inputZeroMask s) +
      maskSize pIn.val.val.1 + maskSize (ShortenedLineResponse.singletonMask i.val) = 4 := by
    rw [constraint_count, hs, residualMask_size, ShortenedLineResponse.singletonMask_size]
  exact (ShortenedWeightedGeometry.singletonTupleEquiv (V := AES.Word) i.val).bijective.comp
    (ShortenedJointGeometry.translation_output_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pIn.val.val.1
      (ShortenedLineResponse.singletonMask i.val) hr (inputZeros_disjoint_residual s) hsize)

/-- At m=2 any chosen retained pair is an actual output information set. -/
theorem pair_retained_projection_bijective (s : Events pOut pIn) (hs : s.val.card = 2)
    (j : RetainedPositions pOut) :
    Function.Bijective (fun c : EventCode s =>
      fun i : {i : RetainedPositions pOut // i ≠ j} => eventRetainedHom s c i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 j
  have hp : maskSize pair = 2 :=
    DoubleUniformGeometry.retainedPairMask_size _ (ThreeActiveGeometry.retainedMask_size pOut) j
  have hr : MaskDisjoint (outputZeroMask s) pair := by
    intro i hi hpair
    exact outputZeros_disjoint_retained s i hi
      ((DoubleUniformGeometry.retainedPairMask_bit _ j i).mp hpair).1
  have hsize : maskSize (outputZeroMask s) + maskSize (inputZeroMask s) + maskSize pair = 4 := by
    rw [constraint_count, hs, hp]
  have hb : Function.Bijective (fun c : EventCode s =>
      fun i : MaskCoordinates pair => wordMixAddEquiv.toAddMonoidHom c.val i.val) :=
    (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pair hr hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective
  exact (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := AES.Word)
    pOut.val.val.1 j).bijective.comp hb

theorem pair_source_projection_bijective (s : Events pOut pIn) (hs : s.val.card = 2)
    (j : RetainedPositions pOut) :
    Function.Bijective (fun uv : EventSource s =>
      fun i : {i : RetainedPositions pOut // i ≠ j} => retainedMap pOut pIn uv.val i.val) := by
  have he :
      (fun uv : EventSource s => fun i : {i : RetainedPositions pOut // i ≠ j} =>
        eventRetainedHom s (eventSourceEquiv s uv) i.val) =
      (fun uv : EventSource s => fun i : {i : RetainedPositions pOut // i ≠ j} =>
        retainedMap pOut pIn uv.val i.val) := by
    funext uv i
    rw [eventRetainedHom_apply]
    rfl
  rw [← he]
  exact (pair_retained_projection_bijective s hs j).comp (eventSourceEquiv s).bijective

/-- Three selected events are exactly the full physical event set. -/
theorem triple_eq_all_events (s : Events pOut pIn) (hs : s.val.card = 3) :
    s.val = eventPositions pOut pIn := by
  apply Finset.eq_of_subset_of_card_le s.property.1
  exact le_of_eq ((eventPositions_card pOut pIn).trans hs.symm)

theorem triple_eventConditions_source_iff (s : Events pOut pIn) (hs : s.val.card = 3)
    (u : ResidualPositions pIn → AES.Word) (v : SourceUniformPositions pIn → AES.Word) :
    eventConditions s (source pIn u v) ↔ v = 0 ∧ omittedValue pOut pIn (u, v) = 0 := by
  rw [eventConditions_source_iff]
  have hall := triple_eq_all_events s hs
  constructor
  · rintro ⟨hi, ho⟩
    constructor
    · funext j
      apply hi j
      rw [hall]
      exact (eventPositions_input_uniform pOut pIn j.val.val).mpr ⟨j, rfl⟩
    · apply ho
      rw [hall]
      exact (eventPositions_output pOut pIn _).mpr rfl
  · rintro ⟨hv, hz⟩
    exact ⟨fun j _ => congrFun hv j, fun _ => hz⟩

theorem triple_code_card (s : Events pOut pIn) (hs : s.val.card = 3) :
    Fintype.card (EventCode s) = Fintype.card AES.Word := by
  simpa only [hs, show (4 : ℕ) - 3 = 1 by decide, pow_one] using eventCode_card s

theorem triple_source_card (s : Events pOut pIn) (hs : s.val.card = 3) :
    Fintype.card (EventSource s) = Fintype.card AES.Word :=
  (Fintype.card_congr (eventSourceEquiv s)).trans (triple_code_card s hs)

/-- Any retained output coordinate parameterizes the actual endpoint line. -/
theorem triple_output_bijective (s : Events pOut pIn) (hs : s.val.card = 3)
    (i : RetainedPositions pOut) :
    Function.Bijective (fun c : EventCode s => eventRetainedHom s c i) := by
  have hi : maskBit (outputZeroMask s) i.val ≠ true := by
    intro hi
    exact outputZeros_disjoint_retained s i.val hi i.property
  exact (ShortenedLineResponse.output_coordinate_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s)
    ((constraint_count s).trans hs) i.val hi).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective

theorem triple_source_output_bijective (s : Events pOut pIn) (hs : s.val.card = 3)
    (i : RetainedPositions pOut) :
    Function.Bijective (fun uv : EventSource s => retainedMap pOut pIn uv.val i) := by
  have he :
      (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv) i) =
      (fun uv : EventSource s => retainedMap pOut pIn uv.val i) := by
    funext uv
    rw [eventRetainedHom_apply]
    rfl
  rw [← he]
  exact (triple_output_bijective s hs i).comp (eventSourceEquiv s).bijective

theorem triple_residual_coordinate_bijective (s : Events pOut pIn) (hs : s.val.card = 3)
    (i : ResidualPositions pIn) :
    Function.Bijective (fun c : EventCode s => eventResidualHom s c i) := by
  have hi : maskBit (inputZeroMask s) i.val ≠ true := by
    intro hi
    exact inputZeros_disjoint_residual s i.val hi i.property
  exact (ShortenedLineResponse.input_coordinate_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s)
    ((constraint_count s).trans hs) i.val hi).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective

/-- A pair can be restricted injectively to a line without being surjective. -/
theorem triple_residual_pair_injective (s : Events pOut pIn) (hs : s.val.card = 3) :
    Function.Injective (eventResidualHom s) := by
  haveI : Nonempty (ResidualPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [CoupledPairFiber.residualPositions_card]; norm_num)
  let i : ResidualPositions pIn := Classical.choice inferInstance
  intro c d he
  exact (triple_residual_coordinate_bijective s hs i).injective (congrFun he i)

theorem triple_source_residual_pair_injective (s : Events pOut pIn) (hs : s.val.card = 3) :
    Function.Injective (fun uv : EventSource s => uv.val.1) := by
  intro uv uv' he
  apply (eventSourceEquiv s).injective
  apply triple_residual_pair_injective s hs
  rw [eventSourceEquiv_residual, eventSourceEquiv_residual]
  exact he

private theorem sum_square_comp_le {C U : Type*} [Fintype C] [Fintype U]
    (f : C → U) (hf : Function.Injective f) (h : U → ℝ) :
    (∑ c, h (f c) ^ 2) ≤ ∑ u, h u ^ 2 := by
  classical
  calc
    (∑ c, h (f c) ^ 2) = ∑ u ∈ Finset.univ.image f, h u ^ 2 := by
      rw [Finset.sum_image]
      intro c _ d _ he
      exact hf he
    _ ≤ ∑ u ∈ (Finset.univ : Finset U), h u ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => sq_nonneg (h u))
    _ = ∑ u, h u ^ 2 := by simp

theorem triple_code_amplitude_energy_le (s : Events pOut pIn) (hs : s.val.card = 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ c : EventCode s, h (eventResidualHom s c) ^ 2) ≤ ∑ u, h u ^ 2 :=
  sum_square_comp_le (eventResidualHom s) (triple_residual_pair_injective s hs) h

theorem triple_source_amplitude_energy_le (s : Events pOut pIn) (hs : s.val.card = 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) ≤ ∑ u, h u ^ 2 := by
  have he := (eventSourceEquiv s).sum_comp
    (fun c : EventCode s => h (eventResidualHom s c) ^ 2)
  simp_rw [eventSourceEquiv_residual] at he
  exact he.trans_le (triple_code_amplitude_energy_le s hs h)

end Nonempty
end AESConcrete.CoupledPairEventGeometry
