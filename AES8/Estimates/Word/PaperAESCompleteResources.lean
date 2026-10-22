import AES8.Estimates.Word.PaperSharpEntriesComplete
import AES8.Estimates.Word.PaperSharpEntriesByteMaps
import AES8.Consequences.PaperAESFromEntries
import AES8.Reductions.Source.PaperAESSourceOrientations
import AESPaper.StartingWord

/-!
# Certified finite predicates and actual word resources

The complete inventory supplies the ordinary and computable Fourier predicates.
The semantic trace-pairing equality transports the Fourier predicate to the
analytic map. The full-column collision clause uses the current paper's
column-energy route.

This leaf exposes entry and full ordinary source resources. Physical estimates
and recurrence consequences remain in their own consumer leaves. The Complete
import supplies the finite inventory used below. No KS07 premise, custom axiom,
or proof placeholder is introduced.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESCompleteResources
open AESMixing PaperSharpEntriesFinite
set_option autoImplicit false

/-- Direct consumer of the complete ordinary finite inventory. -/
theorem ordinary_raw_bound : OrdinaryRawBound :=
  PaperSharpEntriesComplete.ordinary_raw_bound

/-- Semantic equality of the trace-pairing maps, not a numerical coincidence. -/
theorem fourier_map_eq :
    (fourierMap : Byte → Byte) = (fourierMapHom : Byte → Byte) :=
  funext PaperSharpEntriesFinite.fourierMap_apply

/-- Transport the computed predicate to the analytic interface's exact map. -/
theorem fourier_raw_bound : FourierRawBound fourierMap := by
  rw [fourier_map_eq]
  exact PaperSharpEntriesComplete.fourier_raw_bound

/-- Every ordinary/Fourier residual variant, including both adjoints. -/
theorem residual_entries (adjoint fourier : Bool) (a b : AES.Word) :
    |AESConcrete.WordFourierVariants.variant adjoint fourier b a| <
      (27 / 2^32 : ℝ) := by
  cases fourier
  · cases adjoint
    · change |residualMatrix AES.wordSuperboxKernel 0 b a| < _
      exact (PaperSharpEntriesResidual.ordinary_residual_entry_lt_fourteen
        ordinary_raw_bound false a b).trans (by norm_num)
    · change |residualMatrix AES.wordSuperboxKernel 0 a b| < _
      exact (PaperSharpEntriesResidual.ordinary_residual_entry_lt_fourteen
        ordinary_raw_bound false b a).trans (by norm_num)
  · exact PaperSharpEntriesResidual.simultaneous_fourier_variant_lt_twenty_seven
      fourier_raw_bound adjoint a b

/-- The 14/Q source cap applies to the full ordinary forward column. -/
theorem source_point_lt (a b : AES.Word) (ha : a ≠ 0) :
    AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ) := by
  change AESConcrete.WordOrientationClosure.wordKernel .ordinary .ordinary false b a < _
  exact PaperSharpEntriesProfiles.ordinary_word_entry_lt_fourteen
    ordinary_raw_bound false a b ha

/-- Paper localres:entries-source: the collision clause keeps the full column. -/
theorem entries_source :
    (∀ (adjoint fourier : Bool) (a b : AES.Word),
      |AESConcrete.WordFourierVariants.variant adjoint fourier b a| <
        (27 / 2^32 : ℝ)) ∧
    (∀ a : AES.Word, a ≠ 0 →
      (∑ b, AESPaper.StartingWord.wordLaw a b ^ 2) <
        (17 / (15 * 2^32) : ℝ) ∧
      ∀ b : AES.Word, AESPaper.StartingWord.wordLaw a b < (14 / 2^32 : ℝ)) := by
  refine ⟨residual_entries, ?_⟩
  intro a ha
  refine ⟨?_, fun b => source_point_lt a b ha⟩
  have hcol := PaperAESSource.all_nonzero_column_energy_lt_current
    .ordinary .ordinary false a ha
  rw [AESConcrete.WordOrientationClosure.ordinary_word_kernel] at hcol
  simpa only [AESPaper.StartingWord.wordLaw,
    show (2 : ℝ)^32 = 4294967296 by norm_num] using hcol

/-- Both equal-bit physical resources consume their own certified predicate. -/
theorem mixed_entry (bit : Bool) (y x : AES.Word) :
    |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry :=
  PaperAESFromEntries.mixed_entry ordinary_raw_bound fourier_raw_bound bit y x

#print axioms ordinary_raw_bound
#print axioms fourier_map_eq
#print axioms fourier_raw_bound
#print axioms residual_entries
#print axioms source_point_lt
#print axioms entries_source
#print axioms mixed_entry
end AES8.PaperAESCompleteResources
