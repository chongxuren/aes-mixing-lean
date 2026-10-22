import AESConcrete.CoupledTripleMinorResponse
import AESConcrete.ShortenedJointGeometry
import AESConcrete.RetainedGraphMasks
import AESConcrete.DoubleUniformGeometry
import AESMixing.IncidenceCounting

/-!
# Actual zero-event geometry for a joint residual triple

The two events retain their actual GraphPosition labels: the sole ORIGINAL
uniform input zero and the omitted output zero. No artificial event alphabet
replaces the physical source or its signed joint residual triple.

Every nonempty event source has an injective retained-triple map. A singleton
has q^3 points and bijective residual-triple and retained-triple projections.
The double intersection has q^2 points and a bijective retained-pair
projection; its residual triple is only injective, with a subenergy
inequality. The exact full-joint amplitude equality is guarded by event
cardinality ONE. No factorization, axis-zero, positivity, centering or
cancellation is assumed. There are no response-energy estimates, scalar caps
or physical aggregation.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber
  (ResidualPositions RetainedPositions originalUniformLabel originalUniform_not_residual
    omittedLabel omitted_not_retained residualMask_size)
open AESConcrete.CoupledTripleSource
  (SourceWord source source_uniform source_residual sourceWordEquiv)
open AESConcrete.CoupledTripleMinorResponse (retainedMap)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv retainedHom)
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

/-- The two actual unmarked physical graph positions, with no reindexing. -/
def eventPositions (pOut pIn : SelectedSupport 3 4) : Finset GraphPosition :=
  unmarkedGraphPositions 0 0 pOut.val.val.1 pIn.val.val.1

theorem eventPositions_card (pOut pIn : SelectedSupport 3 4) :
    (eventPositions pOut pIn).card = 2 := by
  rw [eventPositions, unmarkedGraphPositions_card 0 0 _ _
    (zeroMask_disjoint _) (zeroMask_disjoint _),
    ThreeActiveGeometry.retainedMask_size, residualMask_size]
  rw [show maskSize (0 : Fin 16) = 0 by decide]

theorem eventPositions_output (pOut pIn : SelectedSupport 3 4) (i : Fin 4) :
    Sum.inl i ∈ eventPositions pOut pIn ↔ i = omittedLabel pOut := by
  rw [eventPositions, unmarkedGraphPositions_output]
  constructor
  · intro hi
    exact CoupledTripleFiber.nonretained_eq_omitted pOut i hi.2
  · intro hi
    subst i
    exact ⟨zeroMask_not _, omitted_not_retained pOut⟩

theorem eventPositions_input (pOut pIn : SelectedSupport 3 4) (i : Fin 4) :
    Sum.inr i ∈ eventPositions pOut pIn ↔ i = originalUniformLabel pIn := by
  rw [eventPositions, unmarkedGraphPositions_input]
  constructor
  · intro hi
    exact CoupledTripleFiber.nonretained_eq_omitted pIn i hi.2
  · intro hi
    subst i
    exact ⟨zeroMask_not _, originalUniform_not_residual pIn⟩

theorem eventPositions_eq (pOut pIn : SelectedSupport 3 4) :
    eventPositions pOut pIn =
      {Sum.inl (omittedLabel pOut), Sum.inr (originalUniformLabel pIn)} := by
  ext e
  cases e with
  | inl i => simp [eventPositions_output]
  | inr i => simp [eventPositions_input]

def eventsOfSize (pOut pIn : SelectedSupport 3 4) (m : ℕ) :
    Finset (Finset GraphPosition) := (eventPositions pOut pIn).powersetCard m

theorem eventsOfSize_card (pOut pIn : SelectedSupport 3 4) (m : ℕ) :
    (eventsOfSize pOut pIn m).card = Nat.choose 2 m := by
  rw [eventsOfSize, Finset.card_powersetCard, eventPositions_card]

theorem nonempty_family_sizes (pOut pIn : SelectedSupport 3 4) :
    (eventsOfSize pOut pIn 1).card = 2 ∧ (eventsOfSize pOut pIn 2).card = 1 := by
  simp only [eventsOfSize_card]
  norm_num [Nat.choose]

/-- Nonempty subsets of the original physical event positions. -/
abbrev Events (pOut pIn : SelectedSupport 3 4) :=
  {s : Finset GraphPosition // s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 2}

theorem events_of_mem (pOut pIn : SelectedSupport 3 4) (m : ℕ)
    (hm : 1 ≤ m ∧ m ≤ 2) (s : Finset GraphPosition)
    (hs : s ∈ eventsOfSize pOut pIn m) :
    s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 2 := by
  have hh := Finset.mem_powersetCard.mp hs
  exact ⟨hh.1, by omega, by omega⟩

/-- The event `v=0` at the original scalar uniform input label. -/
def inputEvent (pOut pIn : SelectedSupport 3 4) : Events pOut pIn :=
  ⟨{Sum.inr (originalUniformLabel pIn)}, by
    refine ⟨?_, by simp, by simp⟩
    intro e he
    have heq : e = Sum.inr (originalUniformLabel pIn) := Finset.mem_singleton.mp he
    subst e
    exact (eventPositions_input pOut pIn _).mpr rfl⟩

/-- The event at the actual omitted output coordinate. -/
def outputEvent (pOut pIn : SelectedSupport 3 4) : Events pOut pIn :=
  ⟨{Sum.inl (omittedLabel pOut)}, by
    refine ⟨?_, by simp, by simp⟩
    intro e he
    have heq : e = Sum.inl (omittedLabel pOut) := Finset.mem_singleton.mp he
    subst e
    exact (eventPositions_output pOut pIn _).mpr rfl⟩

/-- Both physical exclusions, with neither one discarded. -/
def intersectionEvent (pOut pIn : SelectedSupport 3 4) : Events pOut pIn :=
  ⟨eventPositions pOut pIn, by
    refine ⟨fun _ he => he, ?_, ?_⟩ <;> rw [eventPositions_card] <;> decide⟩

theorem inputEvent_card (pOut pIn : SelectedSupport 3 4) :
    (inputEvent pOut pIn).val.card = 1 := by simp [inputEvent]

theorem outputEvent_card (pOut pIn : SelectedSupport 3 4) :
    (outputEvent pOut pIn).val.card = 1 := by simp [outputEvent]

theorem intersectionEvent_card (pOut pIn : SelectedSupport 3 4) :
    (intersectionEvent pOut pIn).val.card = 2 := eventPositions_card pOut pIn

section Nonempty
variable {pOut pIn : SelectedSupport 3 4}

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
  exact originalUniform_not_residual pIn (he ▸ hE)

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
    (u : ResidualPositions pIn → AES.Word) (v : AES.Word) :
    eventConditions s (source pIn u v) ↔
      (Sum.inr (originalUniformLabel pIn) ∈ s.val → v = 0) ∧
      (Sum.inl (omittedLabel pOut) ∈ s.val →
        CoupledTripleMinorResponse.omittedValue pOut pIn (u, v) = 0) := by
  constructor
  · intro hs
    constructor
    · intro hj
      have hz := hs (Sum.inr (originalUniformLabel pIn)) hj
      change source pIn u v (originalUniformLabel pIn) = 0 at hz
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
      have hi := (eventPositions_input pOut pIn i).mp (s.property.1 he)
      subst i
      change source pIn u v (originalUniformLabel pIn) = 0
      rw [source_uniform]
      exact hinput he

theorem input_eventConditions_source_iff (u : ResidualPositions pIn → AES.Word)
    (v : AES.Word) : eventConditions (inputEvent pOut pIn) (source pIn u v) ↔ v = 0 := by
  rw [eventConditions_source_iff]
  simp [inputEvent]

theorem output_eventConditions_source_iff (u : ResidualPositions pIn → AES.Word)
    (v : AES.Word) : eventConditions (outputEvent pOut pIn) (source pIn u v) ↔
      CoupledTripleMinorResponse.omittedValue pOut pIn (u, v) = 0 := by
  rw [eventConditions_source_iff]
  simp [outputEvent]

abbrev EventCode (s : Events pOut pIn) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)

abbrev EventSource (s : Events pOut pIn) :=
  {uv : SourceWord pIn // eventConditions s (sourceWordEquiv pIn uv)}

instance eventSourceFintype (s : Events pOut pIn) : Fintype (EventSource s) := by
  classical
  exact inferInstance

/-- Identity of actual physical states, through the full-source equivalence. -/
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
  exact (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) (informationMask s)
    (informationMask_disjoint s) (information_size_identity s)).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective

theorem eventRetainedHom_injective (s : Events pOut pIn) :
    Function.Injective (eventRetainedHom s) :=
  ShortenedWeightedGeometry.retainedHom_injective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (informationMask s) (informationMask_disjoint s) (informationMask_spec s).2
    (information_size_identity s)

theorem eventSource_retained_injective (s : Events pOut pIn) :
    Function.Injective (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by
  have he : (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv)) =
      (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by
    funext uv i
    rw [eventRetainedHom_apply]
    rfl
  rw [← he]
  exact (eventRetainedHom_injective s).comp (eventSourceEquiv s).injective

-- This identity is deliberately singleton-only. For two constraints and three
-- residual labels the total is FIVE, so no truncated negative dimension is used.
theorem single_information_size_identity (s : Events pOut pIn) (hs : s.val.card = 1) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) + maskSize pIn.val.val.1 = 4 := by
  rw [constraint_count, hs, residualMask_size]

theorem single_residual_bijective (s : Events pOut pIn) (hs : s.val.card = 1) :
    Function.Bijective (eventResidualHom s) := by
  exact (RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pIn.val.val.1
    (inputZeros_disjoint_residual s) (single_information_size_identity s hs)).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective

theorem single_retained_bijective (s : Events pOut pIn) (hs : s.val.card = 1) :
    Function.Bijective (eventRetainedHom s) := by
  have hsize : maskSize (outputZeroMask s) + maskSize (inputZeroMask s) +
      maskSize pOut.val.val.1 = 4 := by
    rw [constraint_count, hs, ThreeActiveGeometry.retainedMask_size]
  exact (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (outputZeros_disjoint_retained s) hsize).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective

theorem single_source_residual_bijective (s : Events pOut pIn) (hs : s.val.card = 1) :
    Function.Bijective (fun uv : EventSource s => uv.val.1) := by
  have he : (fun uv : EventSource s => eventResidualHom s (eventSourceEquiv s uv)) =
      (fun uv : EventSource s => uv.val.1) := funext (eventSourceEquiv_residual s)
  rw [← he]
  exact (single_residual_bijective s hs).comp (eventSourceEquiv s).bijective

theorem single_source_retained_bijective (s : Events pOut pIn) (hs : s.val.card = 1) :
    Function.Bijective (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by
  have he : (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv)) =
      (fun uv : EventSource s => retainedMap pOut pIn uv.val) := by
    funext uv i
    rw [eventRetainedHom_apply]
    rfl
  rw [← he]
  exact (single_retained_bijective s hs).comp (eventSourceEquiv s).bijective

theorem single_code_card (s : Events pOut pIn) (hs : s.val.card = 1) :
    Fintype.card (EventCode s) = Fintype.card AES.Word ^ 3 := by
  simpa only [hs, show (4 : ℕ) - 1 = 3 by decide] using eventCode_card s

theorem single_source_card (s : Events pOut pIn) (hs : s.val.card = 1) :
    Fintype.card (EventSource s) = Fintype.card AES.Word ^ 3 :=
  (Fintype.card_congr (eventSourceEquiv s)).trans (single_code_card s hs)

/-- Reindex the arbitrary original joint h by a genuine singleton bijection. -/
theorem single_code_amplitude_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ c : EventCode s, h (eventResidualHom s c) ^ 2) = ∑ u, h u ^ 2 :=
  Equiv.sum_comp (Equiv.ofBijective (eventResidualHom s) (single_residual_bijective s hs))
    (fun u => h u ^ 2)

theorem single_source_amplitude_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ∑ u, h u ^ 2 :=
  Equiv.sum_comp (Equiv.ofBijective (fun uv : EventSource s => uv.val.1)
    (single_source_residual_bijective s hs)) (fun u => h u ^ 2)

theorem double_eq_all_events (s : Events pOut pIn) (hs : s.val.card = 2) :
    s.val = eventPositions pOut pIn := by
  apply Finset.eq_of_subset_of_card_le s.property.1
  exact le_of_eq ((eventPositions_card pOut pIn).trans hs.symm)

theorem double_eventConditions_source_iff (s : Events pOut pIn) (hs : s.val.card = 2)
    (u : ResidualPositions pIn → AES.Word) (v : AES.Word) :
    eventConditions s (source pIn u v) ↔
      v = 0 ∧ CoupledTripleMinorResponse.omittedValue pOut pIn (u, v) = 0 := by
  have hin : Sum.inr (originalUniformLabel pIn) ∈ s.val := by
    rw [double_eq_all_events s hs]
    exact (eventPositions_input pOut pIn _).mpr rfl
  have hout : Sum.inl (omittedLabel pOut) ∈ s.val := by
    rw [double_eq_all_events s hs]
    exact (eventPositions_output pOut pIn _).mpr rfl
  rw [eventConditions_source_iff]
  simp only [hin, hout, true_implies]

theorem double_code_card (s : Events pOut pIn) (hs : s.val.card = 2) :
    Fintype.card (EventCode s) = Fintype.card AES.Word ^ 2 := by
  simpa only [hs, show (4 : ℕ) - 2 = 2 by decide] using eventCode_card s

theorem double_source_card (s : Events pOut pIn) (hs : s.val.card = 2) :
    Fintype.card (EventSource s) = Fintype.card AES.Word ^ 2 :=
  (Fintype.card_congr (eventSourceEquiv s)).trans (double_code_card s hs)

/-- Every retained pair is an actual output information set on the plane. -/
theorem double_retained_projection_bijective (s : Events pOut pIn) (hs : s.val.card = 2)
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

theorem double_source_projection_bijective (s : Events pOut pIn) (hs : s.val.card = 2)
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
  exact (double_retained_projection_bijective s hs j).comp (eventSourceEquiv s).bijective

theorem double_source_uniform_zero (s : Events pOut pIn) (hs : s.val.card = 2)
    (uv : EventSource s) : uv.val.2 = 0 :=
  ((double_eventConditions_source_iff s hs uv.val.1 uv.val.2).mp uv.property).1

/-- The original scalar is fixed to zero, so the residual tuple determines
the physical source. Surjectivity onto every residual triple is not asserted. -/
theorem double_source_residual_injective (s : Events pOut pIn) (hs : s.val.card = 2) :
    Function.Injective (fun uv : EventSource s => uv.val.1) := by
  intro uv uv' he
  apply Subtype.ext
  exact Prod.ext he ((double_source_uniform_zero s hs uv).trans
    (double_source_uniform_zero s hs uv').symm)

theorem double_residual_injective (s : Events pOut pIn) (hs : s.val.card = 2) :
    Function.Injective (eventResidualHom s) := by
  intro c d he
  apply (eventSourceEquiv s).symm.injective
  apply double_source_residual_injective s hs
  have hc := eventSourceEquiv_residual s ((eventSourceEquiv s).symm c)
  have hd := eventSourceEquiv_residual s ((eventSourceEquiv s).symm d)
  rw [Equiv.apply_symm_apply] at hc hd
  exact hc.symm.trans (he.trans hd)

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

theorem double_code_amplitude_energy_le (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ c : EventCode s, h (eventResidualHom s c) ^ 2) ≤ ∑ u, h u ^ 2 :=
  sum_square_comp_le (eventResidualHom s) (double_residual_injective s hs) h

theorem double_source_amplitude_energy_le (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) ≤ ∑ u, h u ^ 2 :=
  sum_square_comp_le (fun uv : EventSource s => uv.val.1)
    (double_source_residual_injective s hs) h

end Nonempty
end AESConcrete.CoupledTripleEventGeometry
