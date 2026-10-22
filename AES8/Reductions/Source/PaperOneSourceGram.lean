import AES8.Estimates.Word.PaperWordTwoSwapsVariants
import AES8.Reductions.Source.PaperAESSourceOrientations
import AESPaper.OneSourceEnergies

/-!
# Common-source Gram resources on the current paper route

The column bound comes from the current source-support proof. The second
Gram moment comes from the literal two-swap assembly. Each physical source
permutation preserves the entire double sum; no individual Gram entry is
assumed invariant and no independent output labels are introduced.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperOneSourceGram
open AESMixing
open AESPaper.StartingWord (q)
open AESPaper.OneSourceResidual (R)
open AESPaper.OneSourceEnergies (G)
set_option autoImplicit false
set_option maxRecDepth 100000

theorem residual_column_le (x : AES.Word) : gram R x x ≤ 2 / (15 * q) := by
  have h := (PaperAESSource.residualVariant_column_energy_lt_current false false x).le
  change (∑ y, R y x ^ 2) ≤ 2 / (15 * 4294967296) at h
  simpa only [gram, pow_two, q, show (2 : ℝ)^32 = 4294967296 by norm_num] using h

theorem residual_moment_le :
    (∑ x, ∑ z, gram R x z ^ 2) ≤ (300 / q)^2 := by
  have h := (PaperWordTwoSwapsVariants.variant_gram_moment_lt false false).le
  change (∑ x, ∑ z, gram R x z ^ 2) ≤ (300 / 4294967296)^2 at h
  simpa only [q, show (2 : ℝ)^32 = 4294967296 by norm_num] using h

theorem source_entry_le (k i : Fin 4) (x z : AES.Word) :
    |G k i x z| ≤ 2 / (15 * q) :=
  gram_entry_bound R (2 / (15 * q)) (by norm_num [q]) residual_column_le _ _

theorem source_moment_le (k i : Fin 4) :
    (∑ x, ∑ z, G k i x z ^ 2) ≤ (300 / q)^2 := by
  change (∑ x, ∑ z,
    gram R (AESPaper.BoundarySourceCoordinates.outputEquiv k i x)
      (AESPaper.BoundarySourceCoordinates.outputEquiv k i z)^2) ≤ _
  rw [AESPaper.CappedSourceGram.gram_moment_relabel]
  exact residual_moment_le

end AES8.PaperOneSourceGram
