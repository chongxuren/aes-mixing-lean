import AESPaper.RestrictedSourceSections
import AESPaper.PureBiasStartup
import AESConcrete.RestrictedSourcePushforward

/-!
# Unnormalized marked marginals of the actual boundary law

The shortened source density and the actual boundary restriction have exactly
the same weighted pushforwards. Forward boundary coordinates are used in
source sums; inverse coordinates transport an additional input event to the
boundary law. The marginal mass remains the prescribed-zero event mass.
No normalization, output independence, or signed-response monotonicity occurs.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActualRestrictedSource
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESPaper.RestrictedSourceSections (Source density outputCoordinates)
open AESConcrete.RestrictedMarginalEnergy (marginal)

/-- The input-zero half of shortening is automatic on nonzero source mass. -/
theorem graphConditions_iff_outputZero (b : AES.State) (r z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (x : AES.WordState) (hx : (∏ i, wordLaw (sourceInput b i) (x i)) ≠ 0) :
    graphZeroConditions GroupedRecurrence.boundary.toAddMonoidHom r z x ↔
      ZeroEventMDS.outputZero GroupedRecurrence.boundary.toAddMonoidHom r x := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro i hi
    exact ActualZeroEvents.source_support b x hx i ((ha i).mpr hi)

/-- The full original source, restricted without dividing by the event mass. -/
def fullSource (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (x : AES.WordState) : ℝ :=
  if ZeroEventMDS.outputZero GroupedRecurrence.boundary.toAddMonoidHom r x ∧ event x
    then ∏ i : Fin 4, wordLaw (sourceInput b i) (x i) else 0

theorem fullSource_nonneg (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (x : AES.WordState) :
    0 ≤ fullSource b r event x := by
  unfold fullSource
  split_ifs
  · exact ActualZeroEvents.source_product_nonnegative b x
  · exact le_rfl

/-- Signed test weights are permitted because this is an exact sum identity. -/
theorem shortened_weighted_sum_eq_full (b : AES.State) (r z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] (w : AES.WordState → ℝ) :
    (∑ c : Source r z, w c.val * density b r z (fun c => event c.val) c) =
      ∑ x : AES.WordState, w x * fullSource b r event x := by
  change (∑ c : {x : AES.WordState //
      graphZeroConditions GroupedRecurrence.boundary.toAddMonoidHom r z x},
    w c.val * (if event c.val then ∏ i, wordLaw (sourceInput b i) (c.val i) else 0)) = _
  calc
    _ = ∑ x : AES.WordState,
        if graphZeroConditions GroupedRecurrence.boundary.toAddMonoidHom r z x then
          w x * (if event x then ∏ i, wordLaw (sourceInput b i) (x i) else 0) else 0 :=
      RestrictedSourcePushforward.sum_subtype_eq_restricted_sum _
        (fun x : AES.WordState =>
          w x * (if event x then ∏ i, wordLaw (sourceInput b i) (x i) else 0))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (∏ i, wordLaw (sourceInput b i) (x i)) = 0
      · simp [fullSource, hx]
      · have hg := graphConditions_iff_outputZero b r z ha x hx
        by_cases he : event x
        · rw [if_pos he]
          unfold fullSource
          by_cases hr : ZeroEventMDS.outputZero GroupedRecurrence.boundary.toAddMonoidHom r x
          · rw [if_pos (hg.mpr hr), if_pos (And.intro hr he)]
          · rw [if_neg (fun h => hr (hg.mp h)), if_neg (fun h => hr h.1), mul_zero]
        · unfold fullSource
          have hnot : ¬ (ZeroEventMDS.outputZero
              GroupedRecurrence.boundary.toAddMonoidHom r x ∧ event x) := fun h => he h.2
          rw [if_neg he, if_neg hnot, mul_zero]
          simp only [mul_zero, ite_self]

/-- Every finite marginal preserves the original probability weights. -/
theorem shortened_marginal_eq_full {Y : Type*} [Fintype Y] [DecidableEq Y]
    (b : AES.State) (r z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] (coord : AES.WordState → Y) :
    marginal (fun c : Source r z => coord c.val)
      (density b r z (fun c => event c.val)) = marginal coord (fullSource b r event) := by
  funext y
  have h := shortened_weighted_sum_eq_full b r z ha event
    (fun x => if coord x = y then (1 : ℝ) else 0)
  simpa only [marginal, ite_mul, one_mul, zero_mul] using h

/-- The same restriction written in actual boundary coordinates. The event
on original inputs is transported by the inverse boundary. -/
def boundaryRestriction (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (y : AES.WordState) : ℝ :=
  if (∀ i : Fin 4, maskBit r i = true → y i = 0) ∧
      event (GroupedRecurrence.boundary.symm y)
    then BiasStartup.inputLaw b y else 0

theorem boundaryRestriction_nonneg (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (y : AES.WordState) :
    0 ≤ boundaryRestriction b r event y := by
  unfold boundaryRestriction
  split_ifs
  · exact PureBiasStartup.input_nonnegative b y
  · exact le_rfl

/-- Law relabeling uses the inverse; the source coordinate map is forward. -/
theorem boundaryRestriction_apply_boundary (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (x : AES.WordState) :
    boundaryRestriction b r event (GroupedRecurrence.boundary x) = fullSource b r event x := by
  have hl : BiasStartup.inputLaw b (GroupedRecurrence.boundary x) =
      ∏ i, wordLaw (sourceInput b i) (x i) := by
    rw [BiasStartup.inputLaw, GroupedRecurrence.Pi_apply,
      AddEquiv.symm_apply_apply, StartingWord.grouped_initial_product]
  unfold boundaryRestriction fullSource
  rw [AddEquiv.symm_apply_apply, hl]
  rfl

theorem full_marginal_eq_boundary {Y : Type*} [Fintype Y] [DecidableEq Y]
    (b : AES.State) (r : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (coord : AES.WordState → Y) :
    marginal (fun x => coord (GroupedRecurrence.boundary x)) (fullSource b r event) =
      marginal coord (boundaryRestriction b r event) := by
  funext y
  let F : AES.WordState → ℝ :=
    fun x => if coord x = y then boundaryRestriction b r event x else 0
  have h := Equiv.sum_comp GroupedRecurrence.boundary.toEquiv F
  change (∑ x : AES.WordState, F (GroupedRecurrence.boundary x)) =
    marginal coord (boundaryRestriction b r event) y at h
  rw [← h]
  unfold marginal
  apply Finset.sum_congr rfl
  intro x _
  change (if coord (GroupedRecurrence.boundary x) = y then fullSource b r event x else 0) =
    if coord (GroupedRecurrence.boundary x) = y then
      boundaryRestriction b r event (GroupedRecurrence.boundary x) else 0
  rw [boundaryRestriction_apply_boundary]

/-- Actual boundary coordinates retained by the marked marginal. -/
def markedCoordinates (out : Fin 16) (y : AES.WordState) : MaskCoordinates out → AES.Word :=
  fun i => y i.val

/-- The marginal is a joint-event probability, not a conditional law. -/
def markedMarginal (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (MaskCoordinates out → AES.Word) → ℝ :=
  marginal (markedCoordinates out) (boundaryRestriction b r event)

/-- Exact actual-law interpretation of the shortened marked marginal. -/
theorem shortened_output_marginal_eq_actual (b : AES.State) (r z out : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] :
    marginal (outputCoordinates r z out) (density b r z (fun c => event c.val)) =
      markedMarginal b r out event := by
  calc
    _ = marginal (fun x : AES.WordState => markedCoordinates out (GroupedRecurrence.boundary x))
        (fullSource b r event) :=
      shortened_marginal_eq_full b r z ha event
        (fun x : AES.WordState => markedCoordinates out (GroupedRecurrence.boundary x))
    _ = _ := full_marginal_eq_boundary b r event (markedCoordinates out)

theorem markedMarginal_apply (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (y : MaskCoordinates out → AES.Word) :
    markedMarginal b r out event y = ∑ x : AES.WordState,
      if (∀ i : Fin 4, maskBit r i = true → x i = 0) ∧
          event (GroupedRecurrence.boundary.symm x) ∧ markedCoordinates out x = y
        then BiasStartup.inputLaw b x else 0 := by
  unfold markedMarginal marginal boundaryRestriction
  apply Finset.sum_congr rfl
  intro x _
  by_cases hr : ∀ i : Fin 4, maskBit r i = true → x i = 0
  <;> by_cases he : event (GroupedRecurrence.boundary.symm x)
  <;> by_cases hc : markedCoordinates out x = y <;> simp [hr, he, hc]

theorem markedMarginal_nonneg (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] (y : MaskCoordinates out → AES.Word) :
    0 ≤ markedMarginal b r out event y :=
  RestrictedMarginalEnergy.marginal_nonneg _ _ (boundaryRestriction_nonneg b r event) y

theorem markedMarginal_mass (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → AES.Word, markedMarginal b r out event y) =
      ∑ x : AES.WordState, boundaryRestriction b r event x :=
  ManySourceMarginal.marginal_mass _ _

/-- Additional event indicators can reduce the event mass, without normalization. -/
theorem markedMarginal_mass_le (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → AES.Word, markedMarginal b r out event y) ≤
      ActualZeroEvents.maskMass b r := by
  rw [markedMarginal_mass]
  unfold ActualZeroEvents.maskMass boundaryRestriction
  apply Finset.sum_le_sum
  intro x _
  by_cases hr : ∀ i : Fin 4, maskBit r i = true → x i = 0
  · by_cases he : event (GroupedRecurrence.boundary.symm x)
    · rw [if_pos (And.intro hr he), if_pos hr]
    · rw [if_neg (fun h => he h.2), if_pos hr]
      exact PureBiasStartup.input_nonnegative b x
  · rw [if_neg (fun h => hr h.1), if_neg hr]

/-- With no additional restriction, the mass is exactly the zero-event probability. -/
theorem markedMarginal_mass_unrestricted (b : AES.State) (r out : Fin 16) :
    (∑ y : MaskCoordinates out → AES.Word, markedMarginal b r out (fun _ => True) y) =
      ActualZeroEvents.maskMass b r := by
  rw [markedMarginal_mass]
  simp only [boundaryRestriction, ActualZeroEvents.maskMass, and_true]

theorem markedMarginal_mass_le_point (b : AES.State) (hb : 0 < activeSourceCount b)
    (r out : Fin 16) (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → AES.Word, markedMarginal b r out event y) ≤
      (20/q) ^ maskSize r :=
  (markedMarginal_mass_le b r out event).trans (ActualZeroEvents.maskMass_le b hb r)

/-- Too many prescribed zeros annihilate the actual marked marginal itself. -/
theorem markedMarginal_eq_zero (b : AES.State) (hb : 0 < activeSourceCount b)
    (r out : Fin 16) (hr : activeSourceCount b ≤ maskSize r)
    (event : AES.WordState → Prop) [DecidablePred event] :
    markedMarginal b r out event = 0 := by
  funext y
  have hmass : (∑ v : MaskCoordinates out → AES.Word, markedMarginal b r out event v) ≤ 0 := by
    have h := markedMarginal_mass_le b r out event
    rw [ActualZeroEvents.maskMass_eq_zero b hb r hr] at h
    exact h
  have hle : markedMarginal b r out event y ≤
      ∑ v : MaskCoordinates out → AES.Word, markedMarginal b r out event v :=
    Finset.single_le_sum (fun v _ => markedMarginal_nonneg b r out event v) (Finset.mem_univ y)
  exact le_antisymm (hle.trans hmass) (markedMarginal_nonneg b r out event y)

/-- The actual low-observation marginal energy, with all source weights matched. -/
theorem markedMarginal_energy_le (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → AES.Word, markedMarginal b r out event y ^ 2) ≤
      (20/q) ^ (2 * maskSize r) * (6/(5*q)) ^ maskSize out := by
  rw [← shortened_output_marginal_eq_actual b r z out ha event]
  exact RestrictedSourceSections.marginal_energy_le
    b r z s u out hsu hzu hsize hr hobs ha (fun c => event c.val)

end AESPaper.ActualRestrictedSource
