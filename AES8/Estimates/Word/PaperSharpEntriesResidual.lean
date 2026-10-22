import AES8.Estimates.Word.PaperSharpEntriesProfiles
import AES8.Estimates.Word.PaperWordMixedGram

/-!
# Sharp ordinary and simultaneous-Fourier residual entries

Pointed centering and the existing exact whole-word Fourier identification
consume the graph entry bounds. The finite raw predicates remain explicit
until independently certified. The transpose branch uses the proved transpose
of the actual Fourier conjugation; it needs no new byte predicate family.
Draft only. Constructive mathematics only; no attacks or local execution.
-/

noncomputable section
namespace AES8.PaperSharpEntriesResidual
open AESMixing
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.WordFourierCore (wordConjugate)
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesProfiles

set_option autoImplicit false
set_option maxRecDepth 100000

theorem residual_entry_lt_of_raw_bound
    (o : AESConcrete.ByteOrientations.Orientation) (inverse : Bool) (H : ℝ)
    (hH : 1 / (Fintype.card Word - 1 : ℝ) < H)
    (hentry : ∀ a b : Word, a ≠ 0 → wordKernel o o inverse b a < H)
    (a b : Word) : |residualMatrix (wordKernel o o inverse) 0 b a| < H := by
  have hpoint := word_kernel_pointed o o inverse
  have hPpos : (0 : ℝ) ≤ 1 / (Fintype.card Word - 1 : ℝ) := by
    norm_num [Word, BinaryWord.card, Fintype.card_fun]
  have hpos : 0 < H := lt_of_le_of_lt hPpos hH
  by_cases hb : b = 0
  · subst b
    simpa only [residualMatrix, hpoint.zero_row, activityMatrix,
      if_true, sub_self, abs_zero] using hpos
  · by_cases ha : a = 0
    · subst a
      simpa only [residualMatrix, hpoint.zero_column, activityMatrix,
        if_neg hb, if_true, sub_self, abs_zero] using hpos
    · have hK := hentry a b ha
      have hnonneg := hpoint.nonnegative b a
      simp only [residualMatrix, activityMatrix, if_neg hb, if_neg ha]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem ordinary_residual_entry_lt_fourteen (raw : OrdinaryRawBound)
    (inverse : Bool) (a b : Word) :
    |residualMatrix (wordKernel .ordinary .ordinary inverse) 0 b a| <
      (14 / 2^32 : ℝ) :=
  residual_entry_lt_of_raw_bound .ordinary inverse _
    (by norm_num [Word, BinaryWord.card, Fintype.card_fun])
    (ordinary_word_entry_lt_fourteen raw inverse) a b

theorem fourier_channel_residual_entry_lt_twenty_seven (raw : FourierRawBound fourierMap)
    (inverse : Bool) (a b : Word) :
    |residualMatrix (wordKernel .fourier .fourier inverse) 0 b a| <
      (27 / 2^32 : ℝ) :=
  residual_entry_lt_of_raw_bound .fourier inverse _
    (by norm_num [Word, BinaryWord.card, Fintype.card_fun])
    (fourier_word_entry_lt_twenty_seven raw inverse) a b

/-- The exact physical Fourier identification reverses the diffusion and
relabels both words. Its counting measure is already fixed by that theorem. -/
theorem actual_fourier_residual_entry_lt_twenty_seven
    (raw : FourierRawBound fourierMap) (a b : AES.Word) :
    |wordConjugate (residualMatrix AES.wordSuperboxKernel 0) b a| <
      (27 / 2^32 : ℝ) := by
  change |wordConjugate (residualMatrix (wordKernel .ordinary .ordinary false) 0) b a| < _
  rw [AESConcrete.WordFourierClosure.residual_fourier]
  exact fourier_channel_residual_entry_lt_twenty_seven raw true
    (AESConcrete.WordFourierDiffusion.wordReverse a)
    (AESConcrete.WordFourierDiffusion.wordReverse b)

theorem simultaneous_fourier_variant_lt_twenty_seven
    (raw : FourierRawBound fourierMap) (adjoint : Bool) (a b : AES.Word) :
    |AESConcrete.WordFourierVariants.variant adjoint true b a| <
      (27 / 2^32 : ℝ) := by
  cases adjoint
  · exact actual_fourier_residual_entry_lt_twenty_seven raw a b
  · change |wordConjugate (fun y x => residualMatrix AES.wordSuperboxKernel 0 x y) b a| < _
    rw [AES8.PaperWordMixedGram.wordConjugate_transpose]
    exact actual_fourier_residual_entry_lt_twenty_seven raw b a

end AES8.PaperSharpEntriesResidual
