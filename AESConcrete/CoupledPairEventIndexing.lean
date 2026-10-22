import AESConcrete.CoupledPairMinorResponse
import AESConcrete.CoupledPairEventEnergy

/-!
# Physical indexing and exact source restriction for the coupled pair

Index zero is the omitted output; indices one and two are exactly the original
uniformFirst and uniformSecond labels already used by
CoupledPairMinorResponse. All nonempty index subsets, including the triple
intersection, transport to the actual physical events. Every conditional sum
preserves the same arbitrary signed JOINT amplitude.

Only labels and response identities are established here. Constructive fixed
independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct AES10/14/16 scope.

Energy inequalities, eight-term assembly and physical aggregation are
separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairEventIndexing
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairSource
open AESConcrete.CoupledPairMinorResponse (Retained residualKernel)
open AESConcrete.CoupledPairFiber (ResidualPositions inactiveLabel_not)
open AESConcrete.CoupledPairEventGeometry
open AESConcrete.CoupledPairEventEnergy (sourceEventResponse)
open AESConcrete.ThreeActiveGeometry (omittedLabel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

/-- The order is chosen once; the values remain the original physical labels. -/
def uniformIndexEquiv (pIn : SelectedSupport 2 4) : Fin 2 ≃ SourceUniformPositions pIn :=
  (CoupledPairMinorResponse.uniformIndexEquiv pIn).symm

abbrev PhysicalEvent (pIn : SelectedSupport 2 4) := Unit ⊕ SourceUniformPositions pIn

/-- The omitted output is first, followed by the two original uniform inputs. -/
def indexLabelEquiv (pIn : SelectedSupport 2 4) : Fin 3 ≃ PhysicalEvent pIn where
  toFun := Fin.cases (Sum.inl ()) (fun j => Sum.inr (uniformIndexEquiv pIn j))
  invFun := Sum.elim (fun _ => 0) (fun j => ((uniformIndexEquiv pIn).symm j).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (((uniformIndexEquiv pIn).symm (uniformIndexEquiv pIn j)).succ) = j.succ
      rw [Equiv.symm_apply_apply]
  right_inv e := by
    cases e with
    | inl u => cases u; rfl
    | inr j =>
      change Sum.inr (uniformIndexEquiv pIn ((uniformIndexEquiv pIn).symm j)) = Sum.inr j
      rw [Equiv.apply_symm_apply]

/-- Both directions keep the original input label or the omitted output label. -/
def physicalPositionEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    PhysicalEvent pIn ≃ {e : GraphPosition // e ∈ eventPositions pOut pIn} where
  toFun := fun e => match e with
    | Sum.inl _ => ⟨Sum.inl (omittedLabel pOut),
        (eventPositions_output pOut pIn _).mpr rfl⟩
    | Sum.inr j => ⟨Sum.inr j.val.val,
        (eventPositions_input_uniform pOut pIn _).mpr ⟨j, rfl⟩⟩
  invFun := fun e => match e with
    | ⟨Sum.inl _, _⟩ => Sum.inl ()
    | ⟨Sum.inr i, hi⟩ => Sum.inr
        ⟨⟨i, (eventPositions_input pOut pIn i).mp hi⟩, inactiveLabel_not pIn i⟩
  left_inv e := by
    cases e with
    | inl u => cases u; rfl
    | inr j => rfl
  right_inv e := by
    rcases e with ⟨e, he⟩
    apply Subtype.ext
    cases e with
    | inl i =>
      exact congrArg Sum.inl ((eventPositions_output pOut pIn i).mp he).symm
    | inr i => rfl

def eventPositionEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Fin 3 ≃ {e : GraphPosition // e ∈ eventPositions pOut pIn} :=
  (indexLabelEquiv pIn).trans (physicalPositionEquiv pOut pIn)

def eventPosition (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (i : Fin 3) : GraphPosition := (eventPositionEquiv pOut pIn i).val

@[simp]
theorem eventPosition_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    eventPosition pOut pIn 0 = Sum.inl (omittedLabel pOut) := rfl

@[simp]
theorem eventPosition_succ (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (j : Fin 2) :
    eventPosition pOut pIn j.succ = Sum.inr (uniformIndexEquiv pIn j).val.val := rfl

theorem eventPosition_mem (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (i : Fin 3) : eventPosition pOut pIn i ∈ eventPositions pOut pIn :=
  (eventPositionEquiv pOut pIn i).property

theorem eventPosition_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Function.Injective (eventPosition pOut pIn) := by
  intro i j hij
  exact (eventPositionEquiv pOut pIn).injective (Subtype.ext hij)

theorem eventPosition_surjective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (e : GraphPosition) (he : e ∈ eventPositions pOut pIn) :
    ∃ i : Fin 3, eventPosition pOut pIn i = e := by
  obtain ⟨i, hi⟩ := (eventPositionEquiv pOut pIn).surjective ⟨e, he⟩
  exact ⟨i, congrArg Subtype.val hi⟩

def eventPositionEmbedding (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Fin 3 ↪ GraphPosition :=
  ⟨eventPosition pOut pIn, eventPosition_injective pOut pIn⟩

def positionSet (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : Finset (Fin 3)) : Finset GraphPosition :=
  t.map (eventPositionEmbedding pOut pIn)

@[simp]
theorem positionSet_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : Finset (Fin 3)) : (positionSet pOut pIn t).card = t.card := by
  simp only [positionSet, Finset.card_map]

theorem mem_positionSet (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : Finset (Fin 3)) (e : GraphPosition) :
    e ∈ positionSet pOut pIn t ↔ ∃ i ∈ t, eventPosition pOut pIn i = e := by
  simp only [positionSet, Finset.mem_map, eventPositionEmbedding]
  rfl

@[simp]
theorem eventPosition_mem_positionSet (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) (t : Finset (Fin 3)) (i : Fin 3) :
    eventPosition pOut pIn i ∈ positionSet pOut pIn t ↔ i ∈ t := by
  rw [mem_positionSet]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact (eventPosition_injective pOut pIn hji) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem positionSet_subset (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : Finset (Fin 3)) : positionSet pOut pIn t ⊆ eventPositions pOut pIn := by
  intro e he
  obtain ⟨i, _, rfl⟩ := (mem_positionSet pOut pIn t e).mp he
  exact eventPosition_mem pOut pIn i

theorem positionSet_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Function.Injective (positionSet pOut pIn) := by
  intro t u htu
  apply Finset.ext
  intro i
  rw [← eventPosition_mem_positionSet pOut pIn t i,
    ← eventPosition_mem_positionSet pOut pIn u i, htu]

abbrev IndexSets := {t : Finset (Fin 3) // 1 ≤ t.card ∧ t.card ≤ 3}

def indexedEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : IndexSets) : Events pOut pIn :=
  ⟨positionSet pOut pIn t.val, positionSet_subset pOut pIn t.val,
    by simpa only [positionSet_card] using t.property⟩

@[simp]
theorem indexedEvents_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : IndexSets) : (indexedEvents pOut pIn t).val.card = t.val.card :=
  positionSet_card pOut pIn t.val

theorem mem_indexedEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : IndexSets) (e : GraphPosition) :
    e ∈ (indexedEvents pOut pIn t).val ↔
      ∃ i ∈ t.val, eventPosition pOut pIn i = e :=
  mem_positionSet pOut pIn t.val e

theorem indexedEvents_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4) :
    Function.Injective (indexedEvents pOut pIn) := by
  intro t u htu
  exact Subtype.ext (positionSet_injective pOut pIn (congrArg Subtype.val htu))

/-- Actual event values, evaluated before any finite-source restriction. -/
def eventValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (i : Fin 3) (uv : SourceWord pIn) : AES.Word :=
  graphCoordinate wordMixAddEquiv.toAddMonoidHom (sourceWordEquiv pIn uv)
    (eventPosition pOut pIn i)

private theorem wordMixHom_apply (w : AES.WordState) :
    wordMixAddEquiv.toAddMonoidHom w = wordMixAddEquiv w := rfl

@[simp]
theorem eventValue_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) : eventValue pOut pIn 0 uv =
      CoupledPairMinorResponse.omittedValue pOut pIn uv := by
  change wordMixAddEquiv.toAddMonoidHom (source pIn uv.1 uv.2) (omittedLabel pOut) = _
  rw [wordMixHom_apply]
  rfl

@[simp]
theorem eventValue_succ (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (j : Fin 2) (uv : SourceWord pIn) :
    eventValue pOut pIn j.succ uv = uv.2 (uniformIndexEquiv pIn j) := by
  change source pIn uv.1 uv.2 (uniformIndexEquiv pIn j).val.val = _
  exact source_uniform pIn uv.1 uv.2 (uniformIndexEquiv pIn j)

def indexConditions (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (t : IndexSets) (uv : SourceWord pIn) : Prop :=
  ∀ i ∈ t.val, eventValue pOut pIn i uv = 0

theorem eventConditions_iff_indices (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) (t : IndexSets) (uv : SourceWord pIn) :
    eventConditions (indexedEvents pOut pIn t) (sourceWordEquiv pIn uv) ↔
      indexConditions pOut pIn t uv := by
  constructor
  · intro h i hi
    exact h (eventPosition pOut pIn i)
      ((eventPosition_mem_positionSet pOut pIn t.val i).mpr hi)
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := (mem_positionSet pOut pIn t.val e).mp he
    exact h i hi

theorem all_event_values_zero_iff (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) (uv : SourceWord pIn) :
    (∀ i : Fin 3, eventValue pOut pIn i uv = 0) ↔
      CoupledPairMinorResponse.omittedValue pOut pIn uv = 0 ∧
        ∀ j : SourceUniformPositions pIn, uv.2 j = 0 := by
  constructor
  · intro h
    refine ⟨by simpa only [eventValue_zero] using h 0, ?_⟩
    intro j
    have hj := h (((uniformIndexEquiv pIn).symm j).succ)
    simpa only [eventValue_succ, Equiv.apply_symm_apply] using hj
  · rintro ⟨ho, hu⟩ i
    exact Fin.cases (by simpa only [eventValue_zero] using ho)
      (fun j => by simpa only [eventValue_succ] using hu (uniformIndexEquiv pIn j)) i

/-- The exact two original labels already used in the selected-minor response. -/
@[simp]
theorem eventValue_one (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) :
    eventValue pOut pIn 1 uv = uv.2 (CoupledPairMinorResponse.uniformFirst pIn) :=
  eventValue_succ pOut pIn 0 uv

@[simp]
theorem eventValue_two (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (uv : SourceWord pIn) :
    eventValue pOut pIn 2 uv = uv.2 (CoupledPairMinorResponse.uniformSecond pIn) :=
  eventValue_succ pOut pIn 1 uv

def singleIndexSet (i : Fin 3) : IndexSets := ⟨{i}, by simp⟩

def pairIndexSet (i j : Fin 3) (hij : i ≠ j) : IndexSets :=
  ⟨{i, j}, by simp [hij]⟩

def tripleIndexSet : IndexSets := ⟨Finset.univ, by decide⟩

theorem single_indexedEvents_card (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) (i : Fin 3) :
    (indexedEvents pOut pIn (singleIndexSet i)).val.card = 1 := by
  rw [indexedEvents_card]
  simp only [singleIndexSet, Finset.card_singleton]

theorem pair_indexedEvents_card (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) (i j : Fin 3) (hij : i ≠ j) :
    (indexedEvents pOut pIn (pairIndexSet i j hij)).val.card = 2 := by
  rw [indexedEvents_card]
  simp [pairIndexSet, hij]

theorem triple_indexedEvents_card (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 2 4) :
    (indexedEvents pOut pIn tripleIndexSet).val.card = 3 := by
  rw [indexedEvents_card]
  simp only [tripleIndexSet, Finset.card_univ, Fintype.card_fin]

section ResponseTransport
set_option maxRecDepth 100000
variable (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)

def conditionalResponse (t : IndexSets) (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ := by
  classical
  exact ∑ uv : SourceWord pIn, if indexConditions pOut pIn t uv
    then h uv.1 * residualKernel pOut pIn y uv else 0

/-- Exact full-source/subtype identity, before applying an energy estimate. -/
theorem conditionalResponse_eq_sourceEventResponse (t : IndexSets)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    conditionalResponse pOut pIn t h = sourceEventResponse (indexedEvents pOut pIn t) h := by
  classical
  funext y
  unfold conditionalResponse
  have hp (uv : SourceWord pIn) : indexConditions pOut pIn t uv =
      eventConditions (indexedEvents pOut pIn t) (sourceWordEquiv pIn uv) :=
    propext (eventConditions_iff_indices pOut pIn t uv).symm
  simp_rw [hp]
  rw [← Finset.sum_filter]
  calc
    _ = ∑ uv : EventSource (indexedEvents pOut pIn t),
        h uv.val.1 * residualKernel pOut pIn y uv.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := rfl

/-- Any one of the actual three exclusions, with the original joint h. -/
theorem zeroResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ) (i : Fin 3) :
    WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) =
        sourceEventResponse (indexedEvents pOut pIn (singleIndexSet i)) h := by
  rw [← conditionalResponse_eq_sourceEventResponse]
  funext y
  simp [WeightedResponse.zeroResponse, conditionalResponse, indexConditions, singleIndexSet]

/-- Any two distinct exclusions; the selected source subtype is unchanged. -/
theorem intersectionResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (i j : Fin 3) (hij : i ≠ j) :
    TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) (eventValue pOut pIn j) =
        sourceEventResponse (indexedEvents pOut pIn (pairIndexSet i j hij)) h := by
  rw [← conditionalResponse_eq_sourceEventResponse]
  funext y
  simp [TripleResponse.intersectionResponse, conditionalResponse, indexConditions, pairIndexSet]

/-- The triple endpoint follows the uniform-first, uniform-second, omitted order
of EightResponse; its source is a surviving line, not a zero response. -/
theorem tripleIntersectionResponse_eq (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    EightResponse.tripleIntersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn 1) (eventValue pOut pIn 2)
      (eventValue pOut pIn 0) =
        sourceEventResponse (indexedEvents pOut pIn tripleIndexSet) h := by
  rw [← conditionalResponse_eq_sourceEventResponse]
  funext y
  simp [EightResponse.tripleIntersectionResponse, conditionalResponse,
    indexConditions, tripleIndexSet, Fin.forall_fin_succ,
    CoupledPairMinorResponse.uniformFirst, CoupledPairMinorResponse.uniformSecond,
    uniformIndexEquiv, and_comm, and_left_comm]

end ResponseTransport
end AESConcrete.CoupledPairEventIndexing
