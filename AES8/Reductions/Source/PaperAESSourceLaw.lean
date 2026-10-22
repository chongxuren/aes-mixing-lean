import AES8.Math.PaperSourceZeroEvents
import AESConcrete.ActualZeroEventProbabilities
import AESConcrete.AllColumnBound

/-!
# Actual AES source laws and physical zero masks

This is the concrete identification step in `lem:marginals` and Section 11.
The independent laws are the literal byte-channel columns. Inactive input
columns are point masses at zero, so removing their factors gives exactly
the generic `originalLaw`, without conditioning. The generic exact-zero
sets and the concrete sixteen masks consequently describe identical events.
This module proves identities only; it assumes no event or energy bound.
Constructive scope only; no attacks or numerical searches.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word inputColumn)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_apply)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)
open PaperRestrictedDiffusion

attribute [local instance] Classical.propDecidable

/-- Physical coordinates named by a concrete four-bit mask. -/
def maskSet (r : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => maskBit r i = true)

@[simp] theorem mem_maskSet (r : Fin 16) (i : Fin 4) :
    i ∈ maskSet r ↔ maskBit r i = true := by simp [maskSet]

@[simp] theorem maskSet_card (r : Fin 16) : (maskSet r).card = maskSize r := rfl

theorem maskSet_injective : Function.Injective maskSet := by
  intro r s h
  apply maskBitsEquiv.injective
  funext i
  change maskBit r i = maskBit s i
  have hi := Finset.ext_iff.mp h i
  simp only [mem_maskSet] at hi
  cases hr : maskBit r i <;> cases hs : maskBit s i <;> simp_all

/-- The sixteen masks are exactly all physical subsets, without multiplicity. -/
def maskSetEquiv : Fin 16 ≃ Finset (Fin 4) :=
  Equiv.ofBijective maskSet
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨maskSet_injective, by simp⟩)

/-- The active set is literally the complement of the input-zero mask. -/
def active (a : Word) : Finset (Fin 4) := (maskSet (inputZeroMask a))ᶜ

@[simp] theorem mem_active (a : Word) (i : Fin 4) : i ∈ active a ↔ a i ≠ 0 := by
  simp [active, inputZeroMask_bit]

theorem active_card (a : Word) : (active a).card = 4 - maskSize (inputZeroMask a) := by
  simp [active, Finset.card_compl]

/-- Each active coordinate retains its actual channel law and original label. -/
def law (right : Orientation) (a : Word) (i : Fin 4) (x : Byte) : ℝ :=
  channel right x (a i)

theorem law_nonneg (right : Orientation) (a : Word) (i : Fin 4) (x : Byte) :
    0 ≤ law right a i x := (channel_resources right).nonnegative _ _

theorem law_mass_one (right : Orientation) (a : Word) (i : Fin 4) :
    (∑ x, law right a i x) = 1 := (channel_resources right).column_sum _

theorem law_point_le (right : Orientation) (a : Word) (i : Fin 4) (hi : i ∈ active a)
    (x : Byte) : law right a i x ≤ (1 / 64 : ℝ) :=
  (channel_resources right).atom _ _ ((mem_active a i).mp hi)

theorem law_collision (right : Orientation) (a : Word) (i : Fin 4)
    (hi : i ∈ active a) : (∑ x, law right a i x ^ 2) = (65 / 8192 : ℝ) :=
  (channel_resources right).collision_column _ ((mem_active a i).mp hi)

theorem law_zero (right : Orientation) (a : Word) (i : Fin 4) (hi : i ∈ active a) :
    law right a i 0 = 0 := by
  exact ((channel_resources right).zero_row (a i)).trans (if_neg ((mem_active a i).mp hi))

theorem active_nonempty (a : Word) (ha : a ≠ 0) : (active a).Nonempty := by
  by_contra h
  apply ha
  funext i
  by_contra hi
  exact h ⟨i, (mem_active a i).mpr hi⟩

/-- The actual product column is the embedded active product law pointwise. -/
theorem originalLaw_eq_inputColumn (right : Orientation) (a x : Word) :
    originalLaw (active a) (law right a) x = inputColumn right a x := by
  by_cases hs : ∀ i ∉ active a, x i = 0
  · rw [originalLaw, if_pos hs, productWeight, AESConcrete.WordColumnGram.inputColumn_eq_product]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hai : a i = 0 := by simpa only [mem_active, not_not] using hi
    rw [law, hai, (channel_resources right).zero_column, if_pos (hs i hi)]
  · rw [originalLaw, if_neg hs]
    push Not at hs
    obtain ⟨i, hi, hxi⟩ := hs
    have hai : a i = 0 := by simpa only [mem_active, not_not] using hi
    exact (AESConcrete.WordColumnGram.inputColumn_zero_of_inactive right a x i hai hxi).symm

/-- A generic finite exact-zero set is precisely the concrete mask event. -/
theorem exactZeroSet_eq_maskSet_iff (inverse : Bool) (r : Fin 16) (x : Word) :
    PaperSourceZeroEvents.exactZeroSet (byteDiffusionHom inverse) x = maskSet r ↔
      AESConcrete.ActualZeroEventProbabilities.exactOutputZeros inverse r x := by
  constructor
  · intro h i
    have hi := Finset.ext_iff.mp h i
    simpa only [PaperSourceZeroEvents.mem_exactZeroSet, mem_maskSet,
      byteDiffusionHom_apply] using hi.symm
  · intro h
    apply Finset.ext
    intro i
    simpa only [PaperSourceZeroEvents.mem_exactZeroSet, mem_maskSet,
      byteDiffusionHom_apply] using (h i).symm

/-- Generic exact masses are the actual AES source probabilities, with no
normalization factor and with each coordinate's original law retained. -/
theorem exactMass_eq_concrete (right : Orientation) (inverse : Bool) (a : Word)
    (r : Fin 16) :
    PaperSourceZeroEvents.exactMass (byteDiffusionHom inverse) (active a)
      (law right a) (maskSet r) =
      AESConcrete.ActualZeroEventProbabilities.exactMass right inverse a r := by
  rw [AESConcrete.ActualZeroEventProbabilities.exactMass_eq_indicator]
  unfold PaperSourceZeroEvents.exactMass
  apply Finset.sum_congr rfl
  intro x _
  simp only [exactZeroSet_eq_maskSet_iff, originalLaw_eq_inputColumn]

/-- Specified-zero events and arbitrary further indicators also agree under
the literal full input law. Other output positions remain unrestricted. -/
theorem eventMass_eq_concrete (right : Orientation) (inverse : Bool) (a : Word)
    (r : Fin 16) (event : Word → Prop) :
    eventMass (byteDiffusionHom inverse) (active a) (maskSet r) (law right a) event =
      ∑ x : Word, if AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x ∧ event x
        then inputColumn right a x else 0 := by
  rw [eventMass_eq_originalLaw]
  apply Finset.sum_congr rfl
  intro x _
  have hz : (∀ i ∈ maskSet r, byteDiffusionHom inverse x i = 0) ↔
      AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x := by
    simp only [mem_maskSet, byteDiffusionHom_apply,
      AESConcrete.RestrictedSourcePushforward.outputZeros]
  simp only [hz, originalLaw_eq_inputColumn]

/-- The response theorem's marginal is the literal joint probability of
specified output zeros, original marked outputs, and the further event. -/
theorem jointMarginal_eq_concrete (right : Orientation) (inverse : Bool) (a : Word)
    (r s : Fin 16) (event : Word → Prop) (y : maskSet s → Byte) :
    paperJointMarginal (byteDiffusionHom inverse) (active a) (maskSet r) (maskSet s)
      (law right a) event y =
      ∑ x : Word, if AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x ∧ event x ∧
        (fun i : maskSet s => byteDiffusionOrientation inverse x i.val) = y
        then inputColumn right a x else 0 := by
  rw [paperJointMarginal_eq_originalLaw]
  apply Finset.sum_congr rfl
  intro x _
  have hz : (∀ i ∈ maskSet r, byteDiffusionHom inverse x i = 0) ↔
      AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x := by
    simp only [mem_maskSet, byteDiffusionHom_apply,
      AESConcrete.RestrictedSourcePushforward.outputZeros]
  simp only [hz, originalLaw_eq_inputColumn]
  simp only [byteDiffusionHom_apply]

end AES8.PaperAESSource
