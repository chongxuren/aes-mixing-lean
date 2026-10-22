/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.RestrictedZeroEvents
import AESConcrete.RestrictedSourcePushforward
import AESConcrete.AllColumnBound

/-!
# Zero-event resources for the original independent byte source

These are unnormalized full-source events. The actual shortened-source
theorems already provide their MDS information sets, density caps and
collisions. This module packages the one- and two-output-zero conclusions
uniformly over every nonzero source label, every byte orientation and both
diffusion directions. No independence of the diffused coordinates is used.

They are event resources for the one-sided word calculation, not a word
entry cap or fourth-moment theorem.  Constructive only; no attacks or local execution.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.WordMixedZeroEvents
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Word inputColumn)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.RestrictedSourcePushforward
open AESConcrete.ActualRestrictedDensity (restrictedSource)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit inputZeroMask_size_lt_four)
open AESConcrete.RestrictedZeroEvents

def fullZeroMass (o : Orientation) (inverse : Bool) (a : Word) (r : Fin 16) : ℝ :=
  ∑ x : Word, if outputZeros inverse r x then inputColumn o a x else 0

/-- Only the intended output zeros restrict the original product law. Its
inactive-input zeros already hold on every nonzero-density source point. -/
theorem fullZeroMass_eq_shortened (o : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    fullZeroMass o inverse a r =
      ∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
        restrictedSource o inverse a r z (fun _ => True) c := by
  have he := shortened_weighted_sum_eq_full o inverse a r z ha
    (fun _ => True) (fun _ => (1 : ℝ))
  simpa only [one_mul, fullWordSource, and_true, fullZeroMass] using he.symm

/-- One diffused coordinate is zero with probability at most the byte
collision constant. The one-active-source case has mass zero by MDS. -/
theorem one_zero_le (o : Orientation) (inverse : Bool) (a : Word) (ha0 : a ≠ 0)
    (r : Fin 16) (hr : maskSize r = 1) :
    fullZeroMass o inverse a r ≤ (65 / 8192 : ℝ) := by
  let z := inputZeroMask a
  have ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true :=
    fun i => (inputZeroMask_bit a i).symm
  have hz : maskSize z < 4 := inputZeroMask_size_lt_four a ha0
  rw [fullZeroMass_eq_shortened o inverse a r z ha]
  by_cases hsmall : maskSize z ≤ 2
  · exact actual_one_zero_mass_le o inverse a r z hr hsmall ha (fun _ => True)
  · have hhigh : 4 ≤ maskSize r + maskSize z := by omega
    rw [actual_restricted_mass_zero o inverse a ha0 r z hhigh (fun _ => True)]
    norm_num

/-- Two distinct diffused coordinates are simultaneously zero with probability
at most point-cap times collision. Two or fewer active sources give mass zero. -/
theorem two_zero_le (o : Orientation) (inverse : Bool) (a : Word) (ha0 : a ≠ 0)
    (r : Fin 16) (hr : maskSize r = 2) :
    fullZeroMass o inverse a r ≤ (1 / 64 : ℝ) * (65 / 8192) := by
  let z := inputZeroMask a
  have ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true :=
    fun i => (inputZeroMask_bit a i).symm
  rw [fullZeroMass_eq_shortened o inverse a r z ha]
  by_cases hz0 : maskSize z = 0
  · exact (actual_four_active_two_zero_mass_le o inverse a r z hr hz0 ha
      (fun _ => True)).trans (by norm_num)
  by_cases hz1 : maskSize z = 1
  · exact actual_three_active_two_zero_mass_le o inverse a r z hr hz1 ha (fun _ => True)
  · have hhigh : 4 ≤ maskSize r + maskSize z := by omega
    rw [actual_restricted_mass_zero o inverse a ha0 r z hhigh (fun _ => True)]
    norm_num

end AES8.WordMixedZeroEvents
