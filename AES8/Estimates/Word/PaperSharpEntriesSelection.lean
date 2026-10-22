import AES8.Estimates.Word.PaperSharpEntriesAffineSections
import AES8.Estimates.Word.PaperSharpEntriesReduction

/-!
# Select balanced physical five-sets, with homogeneous extreme cases

The selected positions are actual active input/output positions. The remaining
active positions form the fixed complement. When a balanced split is impossible,
three homogeneous zero constraints leave exactly five positions and no fixed
complement. This file supplies selection/geometry only; numeric predicates and
their semantic/channel transport remain distinct obligations. Constructive only.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesSelection
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.MDSFiveFactorEntry
open AESConcrete.ShortenedLineResponse (remaining)

set_option autoImplicit false
set_option maxRecDepth 100000

def selected (s t : Fin 16) : GraphPosition → Prop :=
  Sum.elim (fun i => maskBit s i = true) (fun i => maskBit t i = true)

instance (s t : Fin 16) : DecidablePred (selected s t) := by
  intro p
  cases p with
  | inl i => change Decidable (maskBit s i = true); infer_instance
  | inr i => change Decidable (maskBit t i = true); infer_instance

structure Shape (r z s t : Fin 16) : Prop where
  output_available : MaskDisjoint r s
  input_available : MaskDisjoint z t
  five : maskSize s + maskSize t = 5
  branch :
    (maskSize s = 2 ∧ maskSize t = 3) ∨
    (maskSize s = 3 ∧ maskSize t = 2) ∨
    (maskSize r + maskSize z = 3 ∧
      ((maskSize s = 1 ∧ maskSize t = 4) ∨ (maskSize s = 4 ∧ maskSize t = 1)))

instance (r z s t : Fin 16) : Decidable (Shape r z s t) :=
  decidable_of_iff
    (MaskDisjoint r s ∧ MaskDisjoint z t ∧ maskSize s + maskSize t = 5 ∧
      ((maskSize s = 2 ∧ maskSize t = 3) ∨
      (maskSize s = 3 ∧ maskSize t = 2) ∨
      (maskSize r + maskSize z = 3 ∧
        ((maskSize s = 1 ∧ maskSize t = 4) ∨ (maskSize s = 4 ∧ maskSize t = 1)))))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.output_available, h.input_available, h.five, h.branch⟩⟩

set_option maxHeartbeats 8000000 in
theorem balanced_or_homogeneous_masks : ∀ r z : Fin 16,
    maskSize r + maskSize z ≤ 3 → ∃ s t : Fin 16, Shape r z s t := by
  decide

theorem selected_remaining {r z s t : Fin 16} (h : Shape r z s t)
    (p : GraphPosition) (hp : selected s t p) : remaining r z p := by
  cases p with
  | inl i =>
    intro hi
    exact h.output_available i hi hp
  | inr i =>
    intro hi
    exact h.input_available i hi hp

-- The finite mask theorem above uses its explicit computable Decidable instance.
-- Abstract subtype reindexings below may use classical finite enumerations.
attribute [local instance] Classical.propDecidable

abbrev Selected (s t : Fin 16) := {p : GraphPosition // selected s t p}
abbrev Fixed (r z s t : Fin 16) :=
  {p : GraphPosition // remaining r z p ∧ ¬ selected s t p}

instance (r z s t : Fin 16) : Fintype (Fixed r z s t) := Fintype.ofFinite _

def selectedSides (s t : Fin 16) :
    Selected s t ≃ MaskCoordinates s ⊕ MaskCoordinates t where
  toFun p := match p with
    | ⟨Sum.inl i,hi⟩ => Sum.inl ⟨i,hi⟩
    | ⟨Sum.inr i,hi⟩ => Sum.inr ⟨i,hi⟩
  invFun p := match p with
    | Sum.inl i => ⟨Sum.inl i.val,i.property⟩
    | Sum.inr i => ⟨Sum.inr i.val,i.property⟩
  left_inv p := by rcases p with ⟨p,hp⟩; cases p <;> rfl
  right_inv p := by cases p <;> rfl

theorem selected_card (s t : Fin 16) :
    Fintype.card (Selected s t) = maskSize s + maskSize t := by
  rw [Fintype.card_congr (selectedSides s t), Fintype.card_sum,
    maskCoordinates_card, maskCoordinates_card]

def splitRemaining {r z s t : Fin 16} (h : Shape r z s t) :
    Fixed r z s t ⊕ Selected s t ≃ RemainingPosition r z where
  toFun p := match p with
    | Sum.inl p => ⟨p.val,p.property.1⟩
    | Sum.inr p => ⟨p.val,selected_remaining h p.val p.property⟩
  invFun p := if hs : selected s t p.val then Sum.inr ⟨p.val,hs⟩
    else Sum.inl ⟨p.val,p.property,hs⟩
  left_inv p := by
    cases p with
    | inl p => simp only [p.property.2, ↓reduceDIte]
    | inr p => simp only [p.property, ↓reduceDIte]
  right_inv p := by
    dsimp only
    split_ifs <;> rfl

def fiveEquiv {r z s t : Fin 16} (h : Shape r z s t) :
    Fin 5 ≃ Selected s t :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, selected_card, h.five])

def sectionIndex {r z s t : Fin 16} (h : Shape r z s t) :
    Fixed r z s t ⊕ Fin 5 ≃ RemainingPosition r z :=
  (Equiv.sumCongr (Equiv.refl _) (fiveEquiv h)).trans (splitRemaining h)

/-- Side labels are only a reindexing of the selected physical five-set. -/
def sideIndex {r z s t : Fin 16} (h : Shape r z s t) :
    MaskCoordinates s ⊕ MaskCoordinates t ≃ Fin 5 :=
  (selectedSides s t).symm.trans (fiveEquiv h).symm

theorem sectionIndex_output {r z s t : Fin 16} (h : Shape r z s t)
    (i : MaskCoordinates s) :
    (sectionIndex h (Sum.inr (sideIndex h (Sum.inl i)))).val = Sum.inl i.val := by
  simp [sectionIndex, sideIndex, splitRemaining, selectedSides]

theorem sectionIndex_input {r z s t : Fin 16} (h : Shape r z s t)
    (i : MaskCoordinates t) :
    (sectionIndex h (Sum.inr (sideIndex h (Sum.inr i)))).val = Sum.inr i.val := by
  simp [sectionIndex, sideIndex, splitRemaining, selectedSides]

theorem side_sizes_pos {r z s t : Fin 16} (h : Shape r z s t) :
    0 < maskSize s ∧ 0 < maskSize t := by
  rcases h.branch with h | h | ⟨_, h | h⟩ <;> omega

theorem fixed_card_size {r z s t : Fin 16} (h : Shape r z s t) :
    maskSize r + maskSize z + Fintype.card (Fixed r z s t) + 1 = 4 := by
  have hc := Fintype.card_congr (splitRemaining h)
  rw [Fintype.card_sum, selected_card, h.five, remaining_card] at hc
  have hr := maskSize_le_four r
  have hz := maskSize_le_four z
  omega

theorem fixed_empty_of_three_zeros {r z s t : Fin 16} (h : Shape r z s t)
    (hz : maskSize r + maskSize z = 3) : IsEmpty (Fixed r z s t) := by
  have hc : Fintype.card (Fixed r z s t) = 0 := by
    have hs := fixed_card_size h
    omega
  exact Fintype.card_eq_zero_iff.mp hc

/-- The reference section at zero fixed data and zero parameter is the
actual zero graph. This is a projection-uniqueness statement. -/
theorem sectionSource_zero_fixed (inverse : Bool) (r z : Fin 16)
    {I : Type*} [Fintype I] [DecidableEq I]
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4) :
    sectionSource (AESConcrete.ShortenedLineResponse.byteDiffusionHom inverse)
      (AESConcrete.ShortenedLineResponse.byteDiffusionHom_zeroMDS inverse)
      r z idx hsize (fun _ => 0) 0 =
      AESConcrete.ShortenedLineResponse.zeroGraph
        (AESConcrete.ShortenedLineResponse.byteDiffusionHom inverse) r z := by
  apply (projectionEquiv _
    (AESConcrete.ShortenedLineResponse.byteDiffusionHom_zeroMDS inverse)
    r z idx hsize 0).injective
  rw [sectionSource, Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    change 0 = graphCoordinate _ (0 : Fin 4 →
      AESConcrete.ShortenedLineResponse.Byte) (idx (Sum.inl i)).val
    cases (idx (Sum.inl i)).val <;> simp [graphCoordinate]
  · change 0 = graphCoordinate _ (0 : Fin 4 →
      AESConcrete.ShortenedLineResponse.Byte) (idx (Sum.inr 0)).val
    cases (idx (Sum.inr 0)).val <;> simp [graphCoordinate]

/-- With exactly three zero constraints the selected five-set is the whole
remaining graph. Thus fixed data carry no translation into the section. -/
theorem sectionOffset_eq_zero_of_three_zeros (inverse : Bool)
    {r z s t : Fin 16} (h : Shape r z s t)
    (hz : maskSize r + maskSize z = 3)
    (a : Fixed r z s t → AESConcrete.ShortenedLineResponse.Byte) (k : Fin 5) :
    AES8.PaperSharpEntriesAffineSections.sectionOffset inverse r z
      (sectionIndex h) (fixed_card_size h) a k = 0 := by
  letI : IsEmpty (Fixed r z s t) := fixed_empty_of_three_zeros h hz
  have ha : a = fun _ => 0 := funext (fun i => isEmptyElim i)
  rw [ha]
  unfold AES8.PaperSharpEntriesAffineSections.sectionOffset
  rw [sectionSource_zero_fixed]
  cases (sectionIndex h (Sum.inr k)).val <;>
    simp [AESConcrete.ShortenedLineResponse.zeroGraph, graphCoordinate]

end AES8.PaperSharpEntriesSelection
