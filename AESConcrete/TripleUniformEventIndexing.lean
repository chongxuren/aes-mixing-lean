import AESConcrete.FourteenResponse
import AESConcrete.TripleUniformEventEnergy

/-!
# physical indexing of the four, six and four proper restrictions

Index zero names the omitted output. The successor indices enumerate the three
original uniform-input labels through an equivalence with its inverse. Every
index is matched pointwise to its physical graph coordinate. Finite index
subsets retain those labels when mapped to the proper-event geometry.

The response transports below identify all fourteen conditional source sums
with the corresponding sourceEventResponse. Normalization, the selected-minor
response identity, physical aggregation and inventory composition are
separate. Independent uniform retained keys, whitening, omitted final
MixColumns, ordered-distinct reference pairs and the fixed AES 10/14/16 target
remain unchanged. No physical cap is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformEventIndexing
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource
open AESConcrete.TripleUniformFullResponse
  (SourceWord Retained sourceWordEquiv omittedValue residualKernel)
open AESConcrete.TripleUniformEventGeometry
open AESConcrete.TripleUniformEventEnergy (sourceEventResponse)
open AESConcrete.ThreeActiveGeometry (omittedLabel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

/-- The order is chosen once; the values remain the original physical labels. -/
def uniformIndexEquiv (pIn : SelectedSupport 1 4) : Fin 3 ≃ SourceUniformPositions pIn :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, sourceUniformPositions_card])

abbrev PhysicalEvent (pIn : SelectedSupport 1 4) := Unit ⊕ SourceUniformPositions pIn

/-- The omitted output is first, followed by the three original uniform inputs. -/
def indexLabelEquiv (pIn : SelectedSupport 1 4) : Fin 4 ≃ PhysicalEvent pIn where
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
def physicalPositionEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
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

def eventPositionEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Fin 4 ≃ {e : GraphPosition // e ∈ eventPositions pOut pIn} :=
  (indexLabelEquiv pIn).trans (physicalPositionEquiv pOut pIn)

def eventPosition (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : GraphPosition := (eventPositionEquiv pOut pIn i).val

@[simp]
theorem eventPosition_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    eventPosition pOut pIn 0 = Sum.inl (omittedLabel pOut) := rfl

@[simp]
theorem eventPosition_succ (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (j : Fin 3) :
    eventPosition pOut pIn j.succ = Sum.inr (uniformIndexEquiv pIn j).val.val := rfl

theorem eventPosition_mem (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : eventPosition pOut pIn i ∈ eventPositions pOut pIn :=
  (eventPositionEquiv pOut pIn i).property

theorem eventPosition_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (eventPosition pOut pIn) := by
  intro i j hij
  exact (eventPositionEquiv pOut pIn).injective (Subtype.ext hij)

theorem eventPosition_surjective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (e : GraphPosition) (he : e ∈ eventPositions pOut pIn) :
    ∃ i : Fin 4, eventPosition pOut pIn i = e := by
  obtain ⟨i, hi⟩ := (eventPositionEquiv pOut pIn).surjective ⟨e, he⟩
  exact ⟨i, congrArg Subtype.val hi⟩

def eventPositionEmbedding (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Fin 4 ↪ GraphPosition :=
  ⟨eventPosition pOut pIn, eventPosition_injective pOut pIn⟩

def positionSet (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : Finset (Fin 4)) : Finset GraphPosition :=
  t.map (eventPositionEmbedding pOut pIn)

@[simp]
theorem positionSet_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : Finset (Fin 4)) : (positionSet pOut pIn t).card = t.card := by
  simp only [positionSet, Finset.card_map]

theorem mem_positionSet (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : Finset (Fin 4)) (e : GraphPosition) :
    e ∈ positionSet pOut pIn t ↔ ∃ i ∈ t, eventPosition pOut pIn i = e := by
  simp only [positionSet, Finset.mem_map, eventPositionEmbedding]
  rfl

@[simp]
theorem eventPosition_mem_positionSet (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (t : Finset (Fin 4)) (i : Fin 4) :
    eventPosition pOut pIn i ∈ positionSet pOut pIn t ↔ i ∈ t := by
  rw [mem_positionSet]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact (eventPosition_injective pOut pIn hji) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem positionSet_subset (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : Finset (Fin 4)) : positionSet pOut pIn t ⊆ eventPositions pOut pIn := by
  intro e he
  obtain ⟨i, _, rfl⟩ := (mem_positionSet pOut pIn t e).mp he
  exact eventPosition_mem pOut pIn i

theorem positionSet_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (positionSet pOut pIn) := by
  intro t u htu
  apply Finset.ext
  intro i
  rw [← eventPosition_mem_positionSet pOut pIn t i,
    ← eventPosition_mem_positionSet pOut pIn u i, htu]

abbrev ProperIndexSets := {t : Finset (Fin 4) // 1 ≤ t.card ∧ t.card ≤ 3}

def properEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : ProperIndexSets) : ProperEvents pOut pIn :=
  ⟨positionSet pOut pIn t.val, positionSet_subset pOut pIn t.val,
    by simpa only [positionSet_card] using t.property⟩

@[simp]
theorem properEvents_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : ProperIndexSets) : (properEvents pOut pIn t).val.card = t.val.card :=
  positionSet_card pOut pIn t.val

theorem mem_properEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : ProperIndexSets) (e : GraphPosition) :
    e ∈ (properEvents pOut pIn t).val ↔
      ∃ i ∈ t.val, eventPosition pOut pIn i = e :=
  mem_positionSet pOut pIn t.val e

theorem properEvents_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (properEvents pOut pIn) := by
  intro t u htu
  exact Subtype.ext (positionSet_injective pOut pIn (congrArg Subtype.val htu))

/-- Actual event values, evaluated before any finite-source restriction. -/
def eventValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) (uv : SourceWord pIn) : AES.Word :=
  graphCoordinate wordMixAddEquiv.toAddMonoidHom (sourceWordEquiv pIn uv)
    (eventPosition pOut pIn i)

private theorem wordMixHom_apply (w : AES.WordState) :
    wordMixAddEquiv.toAddMonoidHom w = wordMixAddEquiv w := rfl

@[simp]
theorem eventValue_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn) : eventValue pOut pIn 0 uv = omittedValue pOut pIn uv := by
  change wordMixAddEquiv.toAddMonoidHom (source pIn uv.1 uv.2) (omittedLabel pOut) = _
  rw [wordMixHom_apply]
  rfl

@[simp]
theorem eventValue_succ (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (j : Fin 3) (uv : SourceWord pIn) :
    eventValue pOut pIn j.succ uv = uv.2 (uniformIndexEquiv pIn j) := by
  change source pIn uv.1 uv.2 (uniformIndexEquiv pIn j).val.val = _
  exact source_uniform pIn uv.1 uv.2 (uniformIndexEquiv pIn j)

def indexConditions (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (t : ProperIndexSets) (uv : SourceWord pIn) : Prop :=
  ∀ i ∈ t.val, eventValue pOut pIn i uv = 0

theorem eventConditions_iff_indices (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (t : ProperIndexSets) (uv : SourceWord pIn) :
    eventConditions (properEvents pOut pIn t) (sourceWordEquiv pIn uv) ↔
      indexConditions pOut pIn t uv := by
  constructor
  · intro h i hi
    exact h (eventPosition pOut pIn i)
      ((eventPosition_mem_positionSet pOut pIn t.val i).mpr hi)
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := (mem_positionSet pOut pIn t.val e).mp he
    exact h i hi

theorem all_event_values_zero_iff (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (uv : SourceWord pIn) :
    (∀ i : Fin 4, eventValue pOut pIn i uv = 0) ↔
      omittedValue pOut pIn uv = 0 ∧ ∀ j : SourceUniformPositions pIn, uv.2 j = 0 := by
  constructor
  · intro h
    refine ⟨by simpa only [eventValue_zero] using h 0, ?_⟩
    intro j
    have hj := h (((uniformIndexEquiv pIn).symm j).succ)
    simpa only [eventValue_succ, Equiv.apply_symm_apply] using hj
  · rintro ⟨ho, hu⟩ i
    exact Fin.cases (by simpa only [eventValue_zero] using ho)
      (fun j => by simpa only [eventValue_succ] using hu (uniformIndexEquiv pIn j)) i

/-- The closed index arrays use the same lexicographic order as FourteenResponse. -/
def pairIndices : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

def tripleIndices : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}]

theorem pairIndices_card (i : Fin 6) : (pairIndices i).card = 2 := by
  fin_cases i <;> decide

theorem tripleIndices_card (i : Fin 4) : (tripleIndices i).card = 3 := by
  fin_cases i <;> decide

theorem pairIndices_injective : Function.Injective pairIndices := by decide
theorem tripleIndices_injective : Function.Injective tripleIndices := by decide

def singleIndexSet (i : Fin 4) : ProperIndexSets := ⟨{i}, by simp⟩
def pairIndexSet (i : Fin 6) : ProperIndexSets :=
  ⟨pairIndices i, by rw [pairIndices_card]; norm_num⟩
def tripleIndexSet (i : Fin 4) : ProperIndexSets :=
  ⟨tripleIndices i, by rw [tripleIndices_card]; norm_num⟩

theorem singleIndexSet_injective : Function.Injective singleIndexSet := by
  intro i j hij
  simpa only [singleIndexSet, Finset.singleton_inj] using congrArg Subtype.val hij

theorem pairIndexSet_injective : Function.Injective pairIndexSet := by
  intro i j hij
  exact pairIndices_injective (congrArg Subtype.val hij)

theorem tripleIndexSet_injective : Function.Injective tripleIndexSet := by
  intro i j hij
  exact tripleIndices_injective (congrArg Subtype.val hij)

def singleEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : ProperEvents pOut pIn := properEvents pOut pIn (singleIndexSet i)
def pairEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 6) : ProperEvents pOut pIn := properEvents pOut pIn (pairIndexSet i)
def tripleEvents (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : ProperEvents pOut pIn := properEvents pOut pIn (tripleIndexSet i)

@[simp]
theorem eventPosition_mem_singleEvents (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (i j : Fin 4) :
    eventPosition pOut pIn j ∈ (singleEvents pOut pIn i).val ↔ j = i := by
  change eventPosition pOut pIn j ∈ positionSet pOut pIn {i} ↔ j = i
  rw [eventPosition_mem_positionSet]
  exact Finset.mem_singleton

@[simp]
theorem eventPosition_mem_pairEvents (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (i : Fin 6) (j : Fin 4) :
    eventPosition pOut pIn j ∈ (pairEvents pOut pIn i).val ↔ j ∈ pairIndices i :=
  eventPosition_mem_positionSet pOut pIn (pairIndices i) j

@[simp]
theorem eventPosition_mem_tripleEvents (pOut : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 4) (i j : Fin 4) :
    eventPosition pOut pIn j ∈ (tripleEvents pOut pIn i).val ↔ j ∈ tripleIndices i :=
  eventPosition_mem_positionSet pOut pIn (tripleIndices i) j

@[simp]
theorem singleEvents_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : (singleEvents pOut pIn i).val.card = 1 := by
  simp [singleEvents, properEvents_card, singleIndexSet]

@[simp]
theorem pairEvents_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 6) : (pairEvents pOut pIn i).val.card = 2 := by
  exact (properEvents_card pOut pIn (pairIndexSet i)).trans (pairIndices_card i)

@[simp]
theorem tripleEvents_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (i : Fin 4) : (tripleEvents pOut pIn i).val.card = 3 := by
  exact (properEvents_card pOut pIn (tripleIndexSet i)).trans (tripleIndices_card i)

theorem singleEvents_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (singleEvents pOut pIn) := by
  intro i j hij
  exact singleIndexSet_injective (properEvents_injective pOut pIn hij)

theorem pairEvents_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (pairEvents pOut pIn) := by
  intro i j hij
  exact pairIndexSet_injective (properEvents_injective pOut pIn hij)

theorem tripleEvents_injective (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Function.Injective (tripleEvents pOut pIn) := by
  intro i j hij
  exact tripleIndexSet_injective (properEvents_injective pOut pIn hij)

private theorem indexed_family_eq (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    {n m : ℕ} (f : Fin n → ProperEvents pOut pIn) (hf : Function.Injective f)
    (hm : ∀ i, (f i).val.card = m) (hn : n = Nat.choose 4 m) :
    Finset.univ.image (fun i => (f i).val) = eventsOfSize pOut pIn m := by
  have hval : Function.Injective (fun i => (f i).val) := by
    intro i j hij
    exact hf (Subtype.ext hij)
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powersetCard.mpr ⟨(f i).property.1, hm i⟩
  · apply le_of_eq
    rw [eventsOfSize_card, Finset.card_image_of_injective _ hval,
      Finset.card_univ, Fintype.card_fin]
    exact hn.symm

theorem singleEvents_family (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Finset.univ.image (fun i => (singleEvents pOut pIn i).val) =
      eventsOfSize pOut pIn 1 :=
  indexed_family_eq pOut pIn _ (singleEvents_injective pOut pIn)
    (singleEvents_card pOut pIn) (by norm_num [Nat.choose])

theorem pairEvents_family (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Finset.univ.image (fun i => (pairEvents pOut pIn i).val) =
      eventsOfSize pOut pIn 2 :=
  indexed_family_eq pOut pIn _ (pairEvents_injective pOut pIn)
    (pairEvents_card pOut pIn) (by norm_num [Nat.choose])

theorem tripleEvents_family (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    Finset.univ.image (fun i => (tripleEvents pOut pIn i).val) =
      eventsOfSize pOut pIn 3 :=
  indexed_family_eq pOut pIn _ (tripleEvents_injective pOut pIn)
    (tripleEvents_card pOut pIn) (by norm_num [Nat.choose])

section ResponseTransport
set_option maxRecDepth 100000
variable (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)

def conditionalResponse (t : ProperIndexSets) (h : AES.Word → ℝ)
    (y : Retained pOut → AES.Word) : ℝ := by
  classical
  exact ∑ uv : SourceWord pIn, if indexConditions pOut pIn t uv
    then h uv.1 * residualKernel pOut pIn y uv else 0

/-- Exact counting-source transport; no source point or amplitude is removed. -/
theorem conditionalResponse_eq_sourceEventResponse (t : ProperIndexSets) (h : AES.Word → ℝ) :
    conditionalResponse pOut pIn t h = sourceEventResponse (properEvents pOut pIn t) h := by
  classical
  funext y
  unfold conditionalResponse
  have hp (uv : SourceWord pIn) : indexConditions pOut pIn t uv =
      eventConditions (properEvents pOut pIn t) (sourceWordEquiv pIn uv) :=
    propext (eventConditions_iff_indices pOut pIn t uv).symm
  simp_rw [hp]
  rw [← Finset.sum_filter]
  calc
    _ = ∑ uv : EventSource (properEvents pOut pIn t),
        h uv.val.1 * residualKernel pOut pIn y uv.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := rfl

theorem singleResponses_eq_sourceEventResponse (h : AES.Word → ℝ) (i : Fin 4) :
    FourteenResponse.singleResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i =
        sourceEventResponse (singleEvents pOut pIn i) h := by
  change _ = sourceEventResponse (properEvents pOut pIn (singleIndexSet i)) h
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn (singleIndexSet i) h]
  funext y
  simp [FourteenResponse.singleResponses, WeightedResponse.zeroResponse,
    conditionalResponse, indexConditions, singleIndexSet]

theorem pairResponses_eq_sourceEventResponse (h : AES.Word → ℝ) (i : Fin 6) :
    FourteenResponse.pairResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i =
        sourceEventResponse (pairEvents pOut pIn i) h := by
  change _ = sourceEventResponse (properEvents pOut pIn (pairIndexSet i)) h
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn (pairIndexSet i) h]
  funext y
  fin_cases i <;>
    simp [FourteenResponse.pairResponses, TripleResponse.intersectionResponse,
      conditionalResponse, indexConditions, pairIndexSet, pairIndices]

theorem tripleResponses_eq_sourceEventResponse (h : AES.Word → ℝ) (i : Fin 4) :
    FourteenResponse.tripleResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i =
        sourceEventResponse (tripleEvents pOut pIn i) h := by
  change _ = sourceEventResponse (properEvents pOut pIn (tripleIndexSet i)) h
  rw [← conditionalResponse_eq_sourceEventResponse pOut pIn (tripleIndexSet i) h]
  funext y
  fin_cases i <;>
    simp [FourteenResponse.tripleResponses, FourteenResponse.tripleIntersectionResponse,
      conditionalResponse, indexConditions, tripleIndexSet, tripleIndices]

end ResponseTransport
end AESConcrete.TripleUniformEventIndexing
