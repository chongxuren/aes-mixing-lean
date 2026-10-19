import AESPaper.SeveralSourcePositiveProfile
import AESPaper.OneSourceProfile

/-!
# Universal actual four-round initialization

Initial ShiftRows and the conversion to word coordinates form an additive
equivalence. A nonzero input therefore has at least one active first-layer
source word. Exactly one active source is explicitly represented by the
checked single-word insertion map; all other nonzero inputs have at least
two active sources. These two cases select the independently established
initial profiles without changing the actual law or reference.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.UniversalInitialization
open AESMixing AESConcrete
open AESPaper.StartingWord (sourceInput)
open AESPaper.ManySourceBounds (activeSourceCount activeSourceMask)
open AESPaper.BoundarySourceCoordinates (singleWord)

/-- The source coordinate includes the actual initial ShiftRows, followed
by the established byte-to-word coordinate equivalence. -/
def sourceEquiv : AES.State ≃+ AES.WordState :=
  AES.shiftRowsEquiv.trans AES.transposeState.symm

theorem sourceInput_eq_sourceEquiv (b : AES.State) :
    sourceInput b = sourceEquiv b := rfl

theorem sourceInput_zero : sourceInput (0 : AES.State) = 0 :=
  map_zero sourceEquiv

theorem sourceInput_injective : Function.Injective sourceInput :=
  sourceEquiv.injective

theorem sourceInput_ne_zero (b : AES.State) (hb : b ≠ 0) : sourceInput b ≠ 0 := by
  intro h
  exact hb (sourceInput_injective (h.trans sourceInput_zero.symm))

/-- The active-source count is the cardinality of its exact four-coordinate
support. No AES state values are enumerated. -/
theorem activeSourceCount_eq_card (b : AES.State) :
    activeSourceCount b =
      (Finset.univ.filter (fun i : Fin 4 => sourceInput b i ≠ 0)).card := by
  simp only [activeSourceCount, residualDegree, activeSourceMask, decide_eq_true_eq]

theorem activeSourceCount_pos (b : AES.State) (hb : b ≠ 0) :
    0 < activeSourceCount b := by
  have hx : ∃ i : Fin 4, sourceInput b i ≠ 0 := by
    by_contra h
    push_neg at h
    exact sourceInput_ne_zero b hb (funext h)
  rw [activeSourceCount_eq_card]
  obtain ⟨i, hi⟩ := hx
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

/-- A support of size one gives precisely the source interface required by
the checked one-source law and profile. -/
theorem one_active_source (b : AES.State) (hb : activeSourceCount b = 1) :
    ∃ (k : Fin 4) (a : AES.Word), a ≠ 0 ∧ sourceInput b = singleWord k a := by
  rw [activeSourceCount_eq_card] at hb
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hb
  have ha : sourceInput b k ≠ 0 := by
    have hm : k ∈ Finset.univ.filter (fun i : Fin 4 => sourceInput b i ≠ 0) := by
      rw [hk]
      exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hm).2
  refine ⟨k, sourceInput b k, ha, ?_⟩
  funext i
  by_cases hi : i = k
  · subst i
    simp [singleWord]
  · have hz : sourceInput b i = 0 := by
      by_contra hne
      have hm : i ∈ Finset.univ.filter (fun i : Fin 4 => sourceInput b i ≠ 0) := by
        simp [hne]
      rw [hk] at hm
      exact hi (Finset.mem_singleton.mp hm)
    simp [singleWord, hi, hz]

/-- The exact actual profile satisfies the five-entry initialization
envelope for every nonzero initial AES difference. -/
theorem physical_initial (b : AES.State) (hb : b ≠ 0) (i : Fin 5) :
    ConcreteProfile.physicalProfile b 0 i ≤ AESPaper.initialEnvelope i := by
  have hp := activeSourceCount_pos b hb
  by_cases h1 : activeSourceCount b = 1
  · obtain ⟨k, a, ha, hs⟩ := one_active_source b h1
    exact OneSourceProfile.physical_initial b k a ha hs i
  · have h2 : 2 ≤ activeSourceCount b := by omega
    exact SeveralSourcePositiveProfile.physical_initial b hb h2 i

open AESMixing.AES AESPaper.ProfileSpace

/-- The remaining operator hypothesis concerns exactly H Pi H Pi, including
the final boundary permutation in `ConcreteProfile.fourRound`. -/
theorem recurrence_of_operator
    (hoperator : ∀ f : ProfileSpace.State, Centered f → ∀ i,
      normalizedProfile (ConcreteProfile.fourRound f) i ≤
        step (normalizedProfile f) i)
    (b : AES.State) (hb : b ≠ 0) (k : ℕ) (i : Fin 5) :
    ConcreteProfile.physicalProfile b (k+1) i ≤
      step (ConcreteProfile.physicalProfile b k) i := by
  unfold ConcreteProfile.physicalProfile
  rw [ConcreteProfile.centeredError_step]
  exact hoperator _ (ConcreteProfile.centeredError_centered _ b hb) i

/-- Initialization has been discharged; the exact repeated operator estimate
remains a hypothesis of this conditional mixing consequence. -/
theorem epsilon_of_operator
    (hoperator : ∀ f : ProfileSpace.State, Centered f → ∀ i,
      normalizedProfile (ConcreteProfile.fourRound f) i ≤
        step (normalizedProfile f) i)
    (k r : ℕ) (hr : 4+4*k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k :=
  ConcreteProfile.epsilon_of_initialization_and_operator physical_initial hoperator k r hr

/-- Conditional two-answer private-view consequence for the same actual
retained-key experiment. General stopping/output postprocessing is separate. -/
theorem private_view_of_operator {R : Type*} [Fintype R]
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (hoperator : ∀ f : ProfileSpace.State, Centered f → ∀ i,
      normalizedProfile (ConcreteProfile.fourRound f) i ≤
        step (normalizedProfile f) i)
    (k r : ℕ) (hr : 4+4*k ≤ r)
    (first : R → AES.State) (choose : R → AES.State → AES.State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) (first t) (choose t)))
      (independentView weight (fun t =>
        adaptiveDifferenceView randomPermutationDifference (fun y => choose t y-first t))) <
      decimalBound k :=
  ConcreteProfile.private_view_of_initialization_and_recurrence weight hw hs physical_initial
    (recurrence_of_operator hoperator) k r hr first choose

end AESPaper.UniversalInitialization
