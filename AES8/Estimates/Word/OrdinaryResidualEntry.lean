/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.ActualWordEntry

/-!
# Ordinary AES residual entries at the ordinary fifth-moment constant

The inherited physical shortened-graph proof supports an orientation-specific
moment. Both ordinary byte legs have exact fifth moment `79/(4*2^32)`, so the
ordinary raw word entry is below `20/2^32`. Pointed centering subtracts another
nonnegative quantity below that same cap and preserves it.

This module supplies an ordinary entry resource only. It does not give
the cap for Fourier variants or prove a first-high output. The output-eight
fiber, conditioning, projection and scalar bridges are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace AES8.OrdinaryResidualEntry
open AESMixing
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.WordEntryGraph (Active leg)
open AESConcrete.ByteFifthMoments (ddtMoment)
attribute [local instance] Classical.propDecidable

/-- Retain the exact ordinary moment, before the inherited uniform rounding. -/
theorem active_leg_fifth (a b : Word) (p : Active a b) :
    (∑ v : Byte, leg .ordinary .ordinary a b p.val v ^ 5) = ddtMoment := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl i =>
    have hb : b i ≠ 0 := fun h => hp ((inputZeroMask_bit b i).mpr h)
    exact AESConcrete.ByteFifthMoments.actual_row_fifth .ordinary (b i) hb
  | inr i =>
    have ha : a i ≠ 0 := fun h => hp ((inputZeroMask_bit a i).mpr h)
    exact AESConcrete.ByteFifthMoments.actual_column_fifth .ordinary (a i) ha

/-- The same physical five-factor MDS proof works in either diffusion direction.
The consumer for the actual forward ordinary AES kernel uses `inverse=false`. -/
theorem word_entry_le_ddt (inverse : Bool) (a b : Word) (ha : a ≠ 0) :
    wordKernel .ordinary .ordinary inverse b a ≤ ddtMoment := by
  rw [AESConcrete.WordEntryGraph.actual_shortened_formula]
  change AESConcrete.MDSFiveFactorEntry.graphResponse (byteDiffusionHom inverse)
    (inputZeroMask b) (inputZeroMask a)
    (fun p => leg .ordinary .ordinary a b p.val) ≤ ddtMoment
  by_cases hz : AES.maskSize (inputZeroMask b) + AES.maskSize (inputZeroMask a) ≤ 3
  · exact AESConcrete.MDSFiveFactorEntry.graphResponse_le_fifth
      (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (inputZeroMask b) (inputZeroMask a) hz
      (fun p => leg .ordinary .ordinary a b p.val)
      (fun p v => AESConcrete.WordEntryGraph.leg_nonneg .ordinary .ordinary a b p.val v)
      (fun p => AESConcrete.WordEntryGraph.leg_mass .ordinary .ordinary a b p.val)
      ddtMoment (fun p => (active_leg_fifth a b p).le)
  · obtain ⟨p⟩ := AESConcrete.WordEntryGraph.active_nonempty_of_input_ne_zero a b ha
    rw [AESConcrete.MDSFiveFactorEntry.graphResponse_zero_of_high_zeros
      (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (inputZeroMask b) (inputZeroMask a) (by omega)
      (fun p => leg .ordinary .ordinary a b p.val) p
      (AESConcrete.WordEntryGraph.active_leg_zero .ordinary .ordinary a b p)]
    norm_num [ddtMoment]

theorem word_entry_lt_twenty (inverse : Bool) (a b : Word) (ha : a ≠ 0) :
    wordKernel .ordinary .ordinary inverse b a < (20 / 4294967296 : ℝ) := by
  exact (word_entry_le_ddt inverse a b ha).trans_lt (by norm_num [ddtMoment])

/-- Ordinary pointed centering preserves the common nonnegative raw-entry cap. -/
theorem residual_entry_lt_twenty (inverse : Bool) (a b : Word) :
    |residualMatrix (wordKernel .ordinary .ordinary inverse) 0 b a| <
      (20 / 4294967296 : ℝ) := by
  have hpoint := word_kernel_pointed .ordinary .ordinary inverse
  by_cases hb : b = 0
  · subst b
    simp only [residualMatrix, hpoint.zero_row, activityMatrix, if_true, sub_self, abs_zero]
    norm_num
  · by_cases ha : a = 0
    · subst a
      simp only [residualMatrix, hpoint.zero_column, activityMatrix, if_neg hb, if_true,
        sub_self, abs_zero]
      norm_num
    · have hK := word_entry_lt_twenty inverse a b ha
      have hnonneg := hpoint.nonnegative b a
      have hPpos : (0 : ℝ) ≤ 1 / (Fintype.card Word - 1 : ℝ) := by
        norm_num [Word, BinaryWord.card, Fintype.card_fun]
      have hPlt : (1 / (Fintype.card Word - 1 : ℝ)) < 20 / 4294967296 := by
        norm_num [Word, BinaryWord.card, Fintype.card_fun]
      simp only [residualMatrix, activityMatrix, if_neg hb, if_neg ha]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem actual_word_residual_entry_lt (a b : AES.Word) :
    |residualMatrix AES.wordSuperboxKernel 0 b a| < (20 / 4294967296 : ℝ) :=
  residual_entry_lt_twenty false a b

theorem actual_word_residual_entry_le (a b : AES.Word) :
    |residualMatrix AES.wordSuperboxKernel 0 b a| ≤ (20 / 4294967296 : ℝ) :=
  (actual_word_residual_entry_lt a b).le

end AES8.OrdinaryResidualEntry
