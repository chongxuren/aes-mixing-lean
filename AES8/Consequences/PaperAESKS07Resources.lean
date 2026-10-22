import AES8.Consequences.PaperAESFromKS07

/-!
# Paper-facing word resources from the cited KS07 premises

Source candidate, 2026-10-22, for paper commit 1906c42e. The two external
upper bounds remain the explicit `KS07Bounds` argument. This leaf packages
their already proved downstream word deductions and the separate collision
resource; the physical estimates and numerical consequences have their own
leaves. It neither constructs the external premise nor resumes its finite
computation. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESKS07Resources
open AESMixing
open PaperKS07AssumedEntries (KS07Bounds)
set_option autoImplicit false

/-- The ordinary upper-bound consequence supplied by the external premise. -/
theorem ordinary_maximum (hKS : KS07Bounds) (a b : AES.Word)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AES.wordSuperboxKernel b a ≤ (53 / (4 * 2^32) : ℝ) :=
  hKS.ordinary_max a b ha hb

/-- The simultaneous normalized trace-Fourier bound in the same premise. -/
theorem fourier_maximum (hKS : KS07Bounds) (a b : AES.Word)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AESConcrete.WordFourierCore.wordConjugate AES.wordSuperboxKernel b a ≤
      (109953193 / (2^22 * 2^32) : ℝ) :=
  hKS.fourier_max a b ha hb

/-- The ordinary nonzero-source point interface used by the initializer. -/
theorem ordinary_bound (hKS : KS07Bounds) : PaperWordEntryBounds.OrdinaryBound :=
  PaperKS07AssumedEntries.ordinary_bound hKS

/-- All four actual residual variants, with both adjoint choices. -/
theorem residual_entries (hKS : KS07Bounds) (adjoint fourier : Bool) (a b : AES.Word) :
    |AESConcrete.WordFourierVariants.variant adjoint fourier b a| <
      (27 / 2^32 : ℝ) :=
  PaperKS07AssumedEntries.variant_entry_lt hKS adjoint fourier a b

/-- The sharper source cap applies to a full ordinary forward column. -/
theorem source_point_lt (hKS : KS07Bounds) (a b : AES.Word) (ha : a ≠ 0) :
    AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ) :=
  PaperKS07AssumedEntries.ordinary_source_entry_lt hKS a b ha

/-- Paper localres:entries-source, retaining the separate full-column collision. -/
theorem entries_source (hKS : KS07Bounds) :
    (∀ (adjoint fourier : Bool) (a b : AES.Word),
      |AESConcrete.WordFourierVariants.variant adjoint fourier b a| <
        (27 / 2^32 : ℝ)) ∧
    (∀ a : AES.Word, a ≠ 0 →
      (∑ b, AESPaper.StartingWord.wordLaw a b ^ 2) <
        (17 / (15 * 2^32) : ℝ) ∧
      ∀ b : AES.Word, AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ)) := by
  refine ⟨residual_entries hKS, ?_⟩
  intro a ha
  refine ⟨?_, fun b => source_point_lt hKS a b ha⟩
  exact (PaperKS07AssumedEntries.entries_source hKS).ordinary_collision a ha

/-- Both equal-bit graph resources reuse the passing KS07 endpoint. -/
theorem mixed_entry (hKS : KS07Bounds) (bit : Bool) (y x : AES.Word) :
    |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry :=
  PaperAESFromKS07.mixed_entry hKS bit y x

#print axioms ordinary_maximum
#print axioms fourier_maximum
#print axioms ordinary_bound
#print axioms residual_entries
#print axioms source_point_lt
#print axioms entries_source
#print axioms mixed_entry
end AES8.PaperAESKS07Resources
