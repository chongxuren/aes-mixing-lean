import AESConcrete.TripleUniformFullResponse
import AESConcrete.ShortenedWeightedFourier
import AESConcrete.RetainedGraphMasks
import AESConcrete.ActivityCodeScalar
import AESMixing.IncidenceCounting

/-!
# geometry of the actual proper four-exclusion restrictions

The four physical events are the omitted output and the three original uniform
inputs. A nonempty subset of at most three events determines its actual
output-zero and input-zero masks. All retained information-set, residual
mixed-information-set and translation projection hypotheses are derived from
these event memberships and the actual selected support types. No actual
geometric bijection is a caller premise.

This module supplies source geometry and raw counting energies only. Generic
Fourier translation geometry is distinct from the stronger ordinary line
geometry at three zeros. Event indexing into FourteenResponse, kernel-response
transports, analytic resources and physical aggregation remain separate. No physical (12,7) cap is supplied. Constructive
only; Independent retained keys, whitening, omitted final MixColumns, ordered-
distinct reference pairs and fixed AES 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformEventGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource
open AESConcrete.TripleUniformFullResponse (SourceWord Retained sourceWordEquiv omittedValue)
open AESConcrete.ThreeActiveGeometry
  (omittedLabel omittedLabel_not_retained retainedMask_size)
open AESConcrete.ShortenedWeightedGeometry
  (ShortenedCode graphEquiv retainedHom amplitude Translation translation)
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

theorem residualMask_size (pIn : SelectedSupport 1 4) : maskSize pIn.val.val.1 = 1 := by
  have hd := pIn.val.property.2
  norm_num at hd
  exact hd

/-- No initial zeros: precisely the unmarked output and original input labels. -/
def eventPositions (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Finset GraphPosition :=
  unmarkedGraphPositions 0 0 pOut.val.val.1 pIn.val.val.1

theorem eventPositions_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    (eventPositions pOut pIn).card = 4 := by
  rw [eventPositions, unmarkedGraphPositions_card 0 0 _ _
    (zeroMask_disjoint _) (zeroMask_disjoint _), retainedMask_size, residualMask_size]
  rw [show maskSize (0 : Fin 16) = 0 by decide]

theorem eventPositions_output (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : Sum.inl i ∈ eventPositions pOut pIn ↔ i = omittedLabel pOut := by
  rw [eventPositions, unmarkedGraphPositions_output]
  constructor
  · intro hi
    exact TripleUniformFullResponse.omittedLabel_eq_of_not_retained pOut i hi.2
  · intro hi
    subst i
    exact ⟨zeroMask_not _, omittedLabel_not_retained pOut⟩

theorem eventPositions_input (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) :
    Sum.inr i ∈ eventPositions pOut pIn ↔ maskBit pIn.val.val.1 i ≠ true := by
  rw [eventPositions, unmarkedGraphPositions_input]
  constructor
  · exact fun hi => hi.2
  · exact fun hi => ⟨zeroMask_not _, hi⟩

/-- Every input event is an original uniform label; the inactive mask is empty. -/
theorem eventPositions_input_uniform
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) (i : Fin 4) :
    Sum.inr i ∈ eventPositions pOut pIn ↔
      ∃ j : SourceUniformPositions pIn, j.val.val = i := by
  rw [eventPositions_input]
  constructor
  · intro hi
    exact ⟨⟨⟨i, hi⟩, inactiveLabel_not pIn i⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact j.val.property

/-- Family cardinality, on physical graph positions rather than an enumeration. -/
def eventsOfSize (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) (m : ℕ) :
    Finset (Finset GraphPosition) := (eventPositions pOut pIn).powersetCard m

theorem eventsOfSize_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) (m : ℕ) :
    (eventsOfSize pOut pIn m).card = Nat.choose 4 m := by
  rw [eventsOfSize, Finset.card_powersetCard, eventPositions_card]

theorem proper_family_sizes (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    (eventsOfSize pOut pIn 1).card = 4 ∧ (eventsOfSize pOut pIn 2).card = 6 ∧
      (eventsOfSize pOut pIn 3).card = 4 := by
  simp only [eventsOfSize_card]
  norm_num [Nat.choose]

/-- The two excluded endpoint families are not part of this type. -/
abbrev ProperEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :=
  {s : Finset GraphPosition // s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 3}

theorem properEvents_of_mem (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ 3) (s : Finset GraphPosition)
    (hs : s ∈ eventsOfSize pOut pIn m) :
    s ⊆ eventPositions pOut pIn ∧ 1 ≤ s.card ∧ s.card ≤ 3 := by
  have hh := Finset.mem_powersetCard.mp hs
  exact ⟨hh.1, by omega, by omega⟩

section Proper
variable {pOut : SelectedSupport 3 4} {pIn : SelectedSupport 1 4}

def outputZeroMask (s : ProperEvents pOut pIn) : Fin 16 := outputPositionMask s.val
def inputZeroMask (s : ProperEvents pOut pIn) : Fin 16 := inputPositionMask s.val

theorem constraint_count (s : ProperEvents pOut pIn) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) = s.val.card :=
  selected_position_count s.val

theorem outputZeros_disjoint_retained (s : ProperEvents pOut pIn) :
    MaskDisjoint (outputZeroMask s) pOut.val.val.1 := by
  intro i hi hout
  have he := (eventPositions_output pOut pIn i).mp
    (s.property.1 ((outputPositionMask_bit s.val i).mp hi))
  exact omittedLabel_not_retained pOut (he ▸ hout)

theorem residual_not_inputZero (s : ProperEvents pOut pIn) :
    maskBit (inputZeroMask s) (residualLabel pIn) ≠ true := by
  intro hi
  have he := (eventPositions_input pOut pIn (residualLabel pIn)).mp
    (s.property.1 ((inputPositionMask_bit s.val (residualLabel pIn)).mp hi))
  exact he (residualLabel_mem pIn)

def informationCount (s : ProperEvents pOut pIn) : Fin 5 :=
  ⟨4 - s.val.card, by have hlo := s.property.2.1; omega⟩

theorem informationCount_le (s : ProperEvents pOut pIn) : informationCount s ≤ 3 := by
  change 4 - s.val.card ≤ (3 : ℕ)
  have hlo := s.property.2.1
  omega

def dependentCount (s : ProperEvents pOut pIn) : Fin 5 := ⟨3 - s.val.card, by omega⟩

theorem dependentCount_le (s : ProperEvents pOut pIn) : dependentCount s ≤ 3 := by
  change 3 - s.val.card ≤ (3 : ℕ)
  omega

-- Choices depend only on physical support and event size, never on h or codeword.
def informationMask (s : ProperEvents pOut pIn) : Fin 16 :=
  RetainedGraphMasks.freeMask 3 (informationCount s) (informationCount_le s) pOut

def dependentMask (s : ProperEvents pOut pIn) : Fin 16 :=
  RetainedGraphMasks.freeMask 3 (dependentCount s) (dependentCount_le s) pOut

theorem informationMask_spec (s : ProperEvents pOut pIn) :
    maskSize (informationMask s) = 4 - s.val.card ∧
      RetainedGraphMasks.Submask (informationMask s) pOut.val.val.1 :=
  RetainedGraphMasks.freeMask_spec 3 (informationCount s) (informationCount_le s) pOut

theorem dependentMask_spec (s : ProperEvents pOut pIn) :
    maskSize (dependentMask s) = 3 - s.val.card ∧
      RetainedGraphMasks.Submask (dependentMask s) pOut.val.val.1 :=
  RetainedGraphMasks.freeMask_spec 3 (dependentCount s) (dependentCount_le s) pOut

theorem informationMask_disjoint (s : ProperEvents pOut pIn) :
    MaskDisjoint (outputZeroMask s) (informationMask s) := by
  intro i hi hinfo
  exact outputZeros_disjoint_retained s i hi ((informationMask_spec s).2 i hinfo)

theorem dependentMask_disjoint (s : ProperEvents pOut pIn) :
    MaskDisjoint (outputZeroMask s) (dependentMask s) := by
  intro i hi hdep
  exact outputZeros_disjoint_retained s i hi ((dependentMask_spec s).2 i hdep)

theorem information_size_identity (s : ProperEvents pOut pIn) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) +
      maskSize (informationMask s) = 4 := by
  have hc := constraint_count s
  have hi := (informationMask_spec s).1
  have hup := s.property.2.2
  omega

theorem dependent_size_identity (s : ProperEvents pOut pIn) :
    maskSize (outputZeroMask s) + maskSize (inputZeroMask s) + 1 +
      maskSize (dependentMask s) = 4 := by
  have hc := constraint_count s
  have hd := (dependentMask_spec s).1
  have hup := s.property.2.2
  omega

/-- Exactly the selected physical event zeros on a four-word state. -/
def eventConditions (s : ProperEvents pOut pIn) (w : AES.WordState) : Prop :=
  ∀ e ∈ s.val, graphCoordinate wordMixAddEquiv.toAddMonoidHom w e = 0

theorem eventConditions_iff (s : ProperEvents pOut pIn) (w : AES.WordState) :
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

/-- The family is literally the three original uniform zeros and the one
omitted-output zero, with whichever physical members occur in s. -/
theorem eventConditions_source_iff (s : ProperEvents pOut pIn)
    (u : AES.Word) (v : SourceUniformPositions pIn → AES.Word) :
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

abbrev EventCode (s : ProperEvents pOut pIn) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)

abbrev EventSource (s : ProperEvents pOut pIn) :=
  {uv : SourceWord pIn // eventConditions s (sourceWordEquiv pIn uv)}

instance eventSourceFintype (s : ProperEvents pOut pIn) : Fintype (EventSource s) := by
  classical
  exact inferInstance

/-- Reindex each actual original-source restriction to its physical shortened code. -/
def eventSourceEquiv (s : ProperEvents pOut pIn) : EventSource s ≃ EventCode s where
  toFun uv := ⟨sourceWordEquiv pIn uv.val, (eventConditions_iff s _).mpr uv.property⟩
  invFun c := ⟨(sourceWordEquiv pIn).symm c.val, by
    rw [Equiv.apply_symm_apply]
    exact (eventConditions_iff s c.val).mp c.property⟩
  left_inv uv := Subtype.ext ((sourceWordEquiv pIn).symm_apply_apply uv.val)
  right_inv c := Subtype.ext ((sourceWordEquiv pIn).apply_symm_apply c.val)

theorem eventCode_card (s : ProperEvents pOut pIn) :
    Fintype.card (EventCode s) = Fintype.card AES.Word ^ (4 - s.val.card) := by
  calc
    _ = Fintype.card (ShortenedGraph wordMixAddEquiv.toAddMonoidHom
        (outputZeroMask s) (inputZeroMask s)) :=
      Fintype.card_congr (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _)
    _ = _ := by
      rw [mds_graph_zero_count wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS,
        constraint_count]

def eventRetainedHom (s : ProperEvents pOut pIn) : EventCode s →+ (Retained pOut → AES.Word) :=
  retainedHom wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s) pOut.val.val.1

@[simp]
theorem eventRetainedHom_apply (s : ProperEvents pOut pIn) (c : EventCode s) (i : Retained pOut) :
    eventRetainedHom s c i = wordMixAddEquiv c.val i.val := by
  change wordMixAddEquiv.toAddMonoidHom c.val i.val = _
  rw [wordMixHom_apply]

theorem eventInformationProjection_bijective (s : ProperEvents pOut pIn) :
    Function.Bijective (fun c : EventCode s =>
      fun i : MaskCoordinates (informationMask s) => wordMixAddEquiv c.val i.val) := by
  have hb := (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) (informationMask s)
    (informationMask_disjoint s) (information_size_identity s)).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective
  change Function.Bijective (fun c : EventCode s =>
    fun i : MaskCoordinates (informationMask s) => wordMixAddEquiv.toAddMonoidHom c.val i.val) at hb
  simpa only [wordMixHom_apply] using hb

theorem eventRetainedHom_injective (s : ProperEvents pOut pIn) :
    Function.Injective (eventRetainedHom s) :=
  ShortenedWeightedGeometry.retainedHom_injective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (informationMask s) (informationMask_disjoint s) (informationMask_spec s).2
    (information_size_identity s)

theorem eventSource_retained_injective (s : ProperEvents pOut pIn) :
    Function.Injective (fun uv : EventSource s =>
      TripleUniformFullResponse.retainedMap pOut pIn uv.val) := by
  have he : (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv)) =
      (fun uv : EventSource s => TripleUniformFullResponse.retainedMap pOut pIn uv.val) := by
    funext uv i
    change wordMixAddEquiv.toAddMonoidHom (source pIn uv.val.1 uv.val.2) i.val =
      wordMixAddEquiv (source pIn uv.val.1 uv.val.2) i.val
    rw [wordMixHom_apply]
  rw [← he]
  exact (eventRetainedHom_injective s).comp (eventSourceEquiv s).injective

/-- Original residual input plus the named 3-m dependent retained outputs. -/
def eventMixedEquiv (s : ProperEvents pOut pIn) :
    EventCode s ≃ AES.Word × (MaskCoordinates (dependentMask s) → AES.Word) :=
  ShortenedWeightedGeometry.mixedResidualEquiv wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) (dependentMask s)
    (residualLabel pIn) (dependentMask_disjoint s) (residual_not_inputZero s)
    (by have hs := dependent_size_identity s; omega)

theorem eventMixedEquiv_residual (s : ProperEvents pOut pIn) (c : EventCode s) :
    (eventMixedEquiv s c).1 = c.val (residualLabel pIn) := rfl

theorem eventResidual_surjective (s : ProperEvents pOut pIn) :
    Function.Surjective (fun c : EventCode s => c.val (residualLabel pIn)) := by
  intro u
  refine ⟨(eventMixedEquiv s).symm (u, 0), ?_⟩
  have he := congrArg Prod.fst ((eventMixedEquiv s).apply_symm_apply (u, 0))
  rw [eventMixedEquiv_residual] at he
  exact he

theorem word_card_real : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
  rw [AES.word_card]
  norm_num [ActivityCodeScalar.q]

/-- Exact raw counting factor, with no premise on signed h or h(0). -/
theorem eventCode_amplitude_energy (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    (∑ c : EventCode s, h (c.val (residualLabel pIn)) ^ 2) =
      ActivityCodeScalar.q ^ (3 - s.val.card) * ∑ u, h u ^ 2 := by
  have he := ShortenedWeightedGeometry.amplitude_energy wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) (dependentMask s)
    (residualLabel pIn) (dependentMask_disjoint s) (residual_not_inputZero s)
    (by have hs := dependent_size_identity s; omega) h
  rw [(dependentMask_spec s).1, word_card_real] at he
  exact he

theorem eventSource_amplitude_energy (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) =
      ActivityCodeScalar.q ^ (3 - s.val.card) * ∑ u, h u ^ 2 := by
  have he := Equiv.sum_comp (eventSourceEquiv s)
    (fun c : EventCode s => h (c.val (residualLabel pIn)) ^ 2)
  have hc (uv : EventSource s) :
      (eventSourceEquiv s uv).val (residualLabel pIn) = uv.val.1 := by
    exact source_residual pIn uv.val.1 uv.val.2
  simp_rw [hc] at he
  exact he.trans (eventCode_amplitude_energy s h)

theorem single_source_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 1)
    (h : AES.Word → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ActivityCodeScalar.q ^ 2 * ∑ u, h u ^ 2 := by
  simpa only [hs] using eventSource_amplitude_energy s h

theorem pair_source_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 2)
    (h : AES.Word → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ActivityCodeScalar.q * ∑ u, h u ^ 2 := by
  simpa only [hs, show (3 : ℕ) - 2 = 1 by decide, pow_one] using
    eventSource_amplitude_energy s h

theorem triple_source_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 3)
    (h : AES.Word → ℝ) :
    (∑ uv : EventSource s, h uv.val.1 ^ 2) = ∑ u, h u ^ 2 := by
  simpa only [hs, Nat.sub_self, pow_zero, one_mul] using eventSource_amplitude_energy s h

/-- The complete residual-zero family projects onto the entire dependent tuple. -/
theorem eventTranslation_projection_bijective (s : ProperEvents pOut pIn) :
    Function.Bijective (ShortenedWeightedGeometry.retainedDependentProjection
      wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
      (dependentMask s) (residualLabel pIn) (dependentMask_spec s).2) :=
  ShortenedWeightedGeometry.retainedDependentProjection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (dependentMask s) (residualLabel pIn) (dependentMask_disjoint s) (dependentMask_spec s).2
    (residual_not_inputZero s) (dependent_size_identity s)

theorem eventFourier_projection_bijective (s : ProperEvents pOut pIn) :
    Function.Bijective
      (fun t : Translation wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)
          (residualLabel pIn) =>
        fun j : IndexedGraphEnergy.DependentCoordinates
            (ShortenedWeightedFourier.physicalFree pOut.val.val.1 (dependentMask s)) =>
          eventRetainedHom s (translation wordMixAddEquiv.toAddMonoidHom
            (outputZeroMask s) (inputZeroMask s) (residualLabel pIn) t) j.val) :=
  ShortenedWeightedFourier.fourierDependentProjection_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (dependentMask s) (residualLabel pIn)
    (ShortenedWeightedFourier.physicalFree pOut.val.val.1 (dependentMask s))
    (dependentMask_disjoint s) (dependentMask_spec s).2
    (ShortenedWeightedFourier.physicalFree_complement _ _)
    (residual_not_inputZero s) (dependent_size_identity s)

-- For m=3 use these actual one-coordinate bijections with the ordinary line
-- theorem. The generic Fourier interface instead has no dependent labels.
theorem triple_residual_bijective (s : ProperEvents pOut pIn) (hs : s.val.card = 3) :
    Function.Bijective (fun c : EventCode s => c.val (residualLabel pIn)) := by
  have hb := (ShortenedLineResponse.input_coordinate_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s)
    ((constraint_count s).trans hs) (residualLabel pIn) (residual_not_inputZero s)).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective
  exact hb

theorem triple_output_bijective (s : ProperEvents pOut pIn) (hs : s.val.card = 3)
    (i : Retained pOut) :
    Function.Bijective (fun c : EventCode s => wordMixAddEquiv c.val i.val) := by
  have hi : maskBit (outputZeroMask s) i.val ≠ true := by
    intro hi
    exact outputZeros_disjoint_retained s i.val hi i.property
  have hb := (ShortenedLineResponse.output_coordinate_bijective wordMixAddEquiv.toAddMonoidHom
    wordMixAddEquiv_zeroMDS (outputZeroMask s) (inputZeroMask s)
    ((constraint_count s).trans hs) i.val hi).comp
      (graphEquiv wordMixAddEquiv.toAddMonoidHom (outputZeroMask s) (inputZeroMask s)).bijective
  change Function.Bijective (fun c : EventCode s => wordMixAddEquiv.toAddMonoidHom c.val i.val) at hb
  simpa only [wordMixHom_apply] using hb

end Proper
end AESConcrete.TripleUniformEventGeometry
