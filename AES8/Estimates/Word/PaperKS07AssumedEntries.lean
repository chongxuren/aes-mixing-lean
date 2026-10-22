import AES8.Estimates.Word.PaperWordEntryBounds
import AES8.Reductions.Source.PaperAESSourceOrientations
import AESConcrete.WordFourierClosure
import AESConcrete.WordFourierVariants
import AES8.Estimates.Word.PaperWordMixedGram
import AESPaper.StartingWord

/-!
# The paper's KS07 entry and ordinary-source deduction

Stage assumption, user direction 2026-10-21: correctly instantiated external
results, including Keliher--Sui, are accepted as explicit hypotheses. This file
proves only the deductions in `12-word-resources.tex`, eq:KS-maxima through
localres:entries-source. It does not prove KS07 or run its finite search.

`KS07Bounds` states exactly the two upper bounds on the actual forward word
channel and its simultaneous normalized trace-Fourier conjugate. It is a Prop
parameter, never an axiom or a typeclass instance. No inverse-diffusion family,
byte mixed-moment certificate, one-sided Fourier bound, or source bound is
assumed. The exact existing whole-word Fourier equality performs the transport.

The word alphabet has size 2^32. Centering subtracts 1/(2^32-1), never 1/255.
The sharper 14/2^32 source conclusion concerns ordinary forward columns only.
Constructive mathematics only; no attacks, numerical search, or local execution.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperKS07AssumedEntries
open AESMixing
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.WordFourierCore (wordConjugate)
open AESConcrete.WordFourierDiffusion (wordReverse wordReverse_self wordReverse_zero)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The two correctly instantiated external KS07 upper bounds. Both indices
are nonzero, exactly as in the paper's eq:KS-maxima. The Fourier operation is
simultaneous conjugation of the full channel, with counting normalization. -/
structure KS07Bounds : Prop where
  ordinary_max : ∀ a b : AES.Word, a ≠ 0 → b ≠ 0 →
    AES.wordSuperboxKernel b a ≤ (53 / (4 * 2^32) : ℝ)
  fourier_max : ∀ a b : AES.Word, a ≠ 0 → b ≠ 0 →
    wordConjugate AES.wordSuperboxKernel b a ≤
      (109953193 / (2^22 * 2^32) : ℝ)

/-- Nonzero indices are preserved by the physical coordinate reversal used
by the exact word Fourier identification. -/
theorem wordReverse_ne_zero (a : AES.Word) (ha : a ≠ 0) : wordReverse a ≠ 0 := by
  intro h
  exact ha (wordReverse.injective (h.trans wordReverse_zero.symm))

/-- Extend the ordinary nonzero/nonzero cap to the zero output row by
pointedness. The input remains nonzero; K(0,0)=1 is not bounded by KS07. -/
theorem ordinary_full_entry_le (h : KS07Bounds) (a b : AES.Word) (ha : a ≠ 0) :
    AES.wordSuperboxKernel b a ≤ (53 / (4 * 2^32) : ℝ) := by
  by_cases hb : b = 0
  · subst b
    rw [AES.word_superbox_pointed.zero_row, if_neg ha]
    norm_num
  · exact h.ordinary_max a b ha hb

/-- The reusable source interface consumed by the current startup chain.
The strict weakening is exactly 53 < 4*14. -/
theorem ordinary_bound (h : KS07Bounds) : PaperWordEntryBounds.OrdinaryBound := by
  intro a b ha
  exact (ordinary_full_entry_le h a b ha).trans_lt (by norm_num)

/-- KS07's actual simultaneous-Fourier cap gives the needed reversed
Fourier-channel bound through an equality, not an additional external input. -/
theorem fourier_channel_entry_le (h : KS07Bounds) (a b : AES.Word)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    wordKernel .fourier .fourier true b a ≤
      (109953193 / (2^22 * 2^32) : ℝ) := by
  have hcap := h.fourier_max (wordReverse a) (wordReverse b)
    (wordReverse_ne_zero a ha) (wordReverse_ne_zero b hb)
  have he : wordConjugate AES.wordSuperboxKernel (wordReverse b) (wordReverse a) =
      wordKernel .fourier .fourier true b a := by
    change wordConjugate (wordKernel .ordinary .ordinary false)
      (wordReverse b) (wordReverse a) = _
    rw [AESConcrete.WordFourierClosure.wordKernel_fourier]
    change wordKernel .fourier .fourier true
      (wordReverse (wordReverse b)) (wordReverse (wordReverse a)) = _
    rw [wordReverse_self, wordReverse_self]
  rw [he] at hcap
  exact hcap

/-- The literal scalar step in the printed centering proof. Pointedness
handles both zero axes, and nonnegativity controls the negative centered part.
This theorem contains no numerical AES entry assumption. -/
theorem pointed_residual_entry_lt
    (K : AES.Word → AES.Word → ℝ) (hpoint : PointedBistochastic K (0 : AES.Word))
    (H : ℝ) (hH : 1 / (Fintype.card AES.Word - 1 : ℝ) < H)
    (hentry : ∀ a b : AES.Word, a ≠ 0 → b ≠ 0 → K b a < H)
    (a b : AES.Word) : |residualMatrix K 0 b a| < H := by
  have hPpos : (0 : ℝ) ≤ 1 / (Fintype.card AES.Word - 1 : ℝ) := by
    norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]
  have hpos : 0 < H := lt_of_le_of_lt hPpos hH
  by_cases hb : b = 0
  · subst b
    simpa only [residualMatrix, hpoint.zero_row, activityMatrix,
      if_true, sub_self, abs_zero] using hpos
  · by_cases ha : a = 0
    · subst a
      simpa only [residualMatrix, hpoint.zero_column, activityMatrix,
        if_neg hb, if_true, sub_self, abs_zero] using hpos
    · have hK := hentry a b ha hb
      have hnonneg := hpoint.nonnegative b a
      simp only [residualMatrix, activityMatrix, if_neg hb, if_neg ha]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A stronger ordinary residual cap, obtained by the same printed scalar
centering argument. Only the 27/2^32 cap is needed for all four variants. -/
theorem ordinary_residual_entry_lt_fourteen (h : KS07Bounds) (a b : AES.Word) :
    |residualMatrix AES.wordSuperboxKernel 0 b a| < (14 / 2^32 : ℝ) := by
  exact pointed_residual_entry_lt AES.wordSuperboxKernel AES.word_superbox_pointed _
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun])
    (fun a b ha _ => ordinary_bound h a b ha) a b

/-- The squared-correlation maximum is below 27/2^32 because
109953193 < 27*2^22. Its nonnegative Fourier-channel representation supplies
exact pointed centering in the reversed coordinates. -/
theorem fourier_channel_residual_entry_lt (h : KS07Bounds) (a b : AES.Word) :
    |residualMatrix (wordKernel .fourier .fourier true) 0 b a| <
      (27 / 2^32 : ℝ) := by
  exact pointed_residual_entry_lt _ (word_kernel_pointed .fourier .fourier true) _
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun])
    (fun a b ha hb => (fourier_channel_entry_le h a b ha hb).trans_lt (by norm_num)) a b

/-- Transport the residual, including its global zero/nonzero-word
projection, using the already proved exact simultaneous Fourier equality. -/
theorem actual_fourier_residual_entry_lt (h : KS07Bounds) (a b : AES.Word) :
    |wordConjugate (residualMatrix AES.wordSuperboxKernel 0) b a| <
      (27 / 2^32 : ℝ) := by
  change |wordConjugate (residualMatrix (wordKernel .ordinary .ordinary false) 0) b a| < _
  rw [AESConcrete.WordFourierClosure.residual_fourier]
  exact fourier_channel_residual_entry_lt h (wordReverse a) (wordReverse b)

/-- The paper's maximum absolute entry bound for all four actual residuals
R, R^T, F R F, and F R^T F. These are the two flags of the existing variant
interface; no independent left/right Fourier choices are asserted here. -/
theorem variant_entry_lt (h : KS07Bounds) (adjoint fourier : Bool) (a b : AES.Word) :
    |AESConcrete.WordFourierVariants.variant adjoint fourier b a| <
      (27 / 2^32 : ℝ) := by
  cases fourier with
  | false =>
    cases adjoint with
    | false =>
      change |residualMatrix AES.wordSuperboxKernel 0 b a| < _
      exact (ordinary_residual_entry_lt_fourteen h a b).trans (by norm_num)
    | true =>
      change |residualMatrix AES.wordSuperboxKernel 0 a b| < _
      exact (ordinary_residual_entry_lt_fourteen h b a).trans (by norm_num)
  | true =>
    cases adjoint with
    | false =>
      exact actual_fourier_residual_entry_lt h a b
    | true =>
      change |wordConjugate (fun y x => residualMatrix AES.wordSuperboxKernel 0 x y) b a| < _
      rw [AES8.PaperWordMixedGram.wordConjugate_transpose]
      exact actual_fourier_residual_entry_lt h b a

/-- The first ordinary forward source has the sharper point-probability
cap. The squared-correlation hypothesis is not used by this deduction. -/
theorem ordinary_source_entry_lt (h : KS07Bounds) (a b : AES.Word) (ha : a ≠ 0) :
    AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ) :=
  ordinary_bound h a b ha

theorem ordinary_source_abs_entry_lt (h : KS07Bounds) (a b : AES.Word) (ha : a ≠ 0) :
    |AESPaper.StartingWord.wordLaw a b| < (14 / 2^32 : ℝ) := by
  rw [abs_of_nonneg (AESPaper.StartingWord.wordLaw_nonnegative a b)]
  exact ordinary_source_entry_lt h a b ha

/-- Pointwise finite-alphabet formulation of localres:entries-source.
The collision estimate comes from the preceding full-column result and is
not an implication of the two KS07 maxima. -/
structure EntrySourceResources : Prop where
  residual_entries : ∀ adjoint fourier : Bool, ∀ a b : AES.Word,
    |AESConcrete.WordFourierVariants.variant adjoint fourier b a| < (27 / 2^32 : ℝ)
  ordinary_source : ∀ a b : AES.Word, a ≠ 0 →
    AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ)
  ordinary_collision : ∀ a : AES.Word, a ≠ 0 →
    (∑ b, AESPaper.StartingWord.wordLaw a b ^ 2) < (17 / (15 * 2^32) : ℝ)

theorem entries_source (h : KS07Bounds) : EntrySourceResources where
  residual_entries := variant_entry_lt h
  ordinary_source := ordinary_source_entry_lt h
  ordinary_collision a ha := by
    have hcol := PaperAESSource.all_nonzero_column_energy_lt_current
      .ordinary .ordinary false a ha
    rw [AESConcrete.WordOrientationClosure.ordinary_word_kernel] at hcol
    simpa only [AESPaper.StartingWord.wordLaw,
      show (2 : ℝ)^32 = 4294967296 by norm_num] using hcol

end AES8.PaperKS07AssumedEntries
