import AESConcrete.ByteFifthMoments
import AESConcrete.MDSFiveFactorEntry
import AESConcrete.WordEntryGraph

/-!
# Actual ordinary word-entry bound

Exact byte fifth moments, physical MDS sections and the full word graph
identity supply the raw entry bound. Pointed centering uses the difference
of two nonnegative quantities below the same cap, preserving the constant.
All explicit left/right byte orientations and both diffusion directions
are covered. Whole-word Fourier identification and one-sided mixed entries
remain separate obligations. Constructive mathematics only; no attacks.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualWordEntry
open AESMixing
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.WordEntryGraph (Active leg)
open AESConcrete.ByteFifthMoments (uniformH)
attribute [local instance] Classical.propDecidable

theorem active_leg_fifth (left right : Orientation) (a b : Word) (p : Active a b) :
    (∑ v : Byte, leg left right a b p.val v ^ 5) ≤ uniformH := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i =>
    have hb : b i ≠ 0 := fun h => hp ((inputZeroMask_bit b i).mpr h)
    exact ByteFifthMoments.actual_row_fifth_le_uniform left (b i) hb
  | inr i =>
    have ha : a i ≠ 0 := fun h => hp ((inputZeroMask_bit a i).mpr h)
    exact ByteFifthMoments.actual_column_fifth_le_uniform right (a i) ha

/-- Nonzero input suffices, including a zero external output. -/
theorem word_entry_le_uniform (left right : Orientation) (inverse : Bool)
    (a b : Word) (ha : a ≠ 0) : wordKernel left right inverse b a ≤ uniformH := by
  rw [WordEntryGraph.actual_shortened_formula]
  change MDSFiveFactorEntry.graphResponse (byteDiffusionHom inverse)
    (inputZeroMask b) (inputZeroMask a) (fun p => leg left right a b p.val) ≤ uniformH
  by_cases hz : AES.maskSize (inputZeroMask b) + AES.maskSize (inputZeroMask a) ≤ 3
  · exact MDSFiveFactorEntry.graphResponse_le_fifth
      (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (inputZeroMask b) (inputZeroMask a) hz
      (fun p => leg left right a b p.val)
      (fun p v => WordEntryGraph.leg_nonneg left right a b p.val v)
      (fun p => WordEntryGraph.leg_mass left right a b p.val)
      uniformH (active_leg_fifth left right a b)
  · obtain ⟨p⟩ := WordEntryGraph.active_nonempty_of_input_ne_zero a b ha
    rw [MDSFiveFactorEntry.graphResponse_zero_of_high_zeros
      (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (inputZeroMask b) (inputZeroMask a) (by omega)
      (fun p => leg left right a b p.val) p
      (WordEntryGraph.active_leg_zero left right a b p)]
    exact ByteFifthMoments.uniformH_pos.le

theorem word_entry_lt (left right : Orientation) (inverse : Bool)
    (a b : Word) (ha : a ≠ 0) :
    wordKernel left right inverse b a < (46/4294967296 : ℝ) := by
  apply (word_entry_le_uniform left right inverse a b ha).trans_lt
  norm_num [uniformH, ByteFifthMoments.walshMoment]

/-- No quantitative resource premise remains in the actual residual bound. -/
theorem residual_entry_lt (left right : Orientation) (inverse : Bool) (a b : Word) :
    |residualMatrix (wordKernel left right inverse) 0 b a| < (46/4294967296 : ℝ) := by
  have hpoint := word_kernel_pointed left right inverse
  by_cases hb : b = 0
  · subst b
    simp only [residualMatrix, hpoint.zero_row, activityMatrix, if_true, sub_self, abs_zero]
    norm_num
  · by_cases ha : a = 0
    · subst a
      simp only [residualMatrix, hpoint.zero_column, activityMatrix, if_neg hb, if_true,
        sub_self, abs_zero]
      norm_num
    · have hK := word_entry_lt left right inverse a b ha
      have hnonneg := hpoint.nonnegative b a
      have hPpos : (0 : ℝ) ≤ 1/(Fintype.card Word - 1 : ℝ) := by
        norm_num [Word, BinaryWord.card, Fintype.card_fun]
      have hPlt : (1/(Fintype.card Word - 1 : ℝ)) < 46/4294967296 := by
        norm_num [Word, BinaryWord.card, Fintype.card_fun]
      simp only [residualMatrix, activityMatrix, if_neg hb, if_neg ha]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem actual_word_residual_entry_lt (a b : Word) :
    |residualMatrix AES.wordSuperboxKernel 0 b a| < (46/4294967296 : ℝ) :=
  residual_entry_lt .ordinary .ordinary false a b

end AESConcrete.ActualWordEntry
