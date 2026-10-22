import AES8.Reductions.Source.PaperAESStartupSource
import AES8.Reductions.Source.PaperAESLocalResources
import AES8.Reductions.Source.PaperOneSourceGram
import AES8.Reductions.Source.OneSourceSupport
import AES8.Estimates.Source.PaperStartupScalars
import AESPaper.OneSourceBounds

/-!
# The one-source full-support startup refinement

All four boundary outputs are bijective images of one original word label.
The exact pattern Gram identity and the generic capped-source argument are
reused. The point cap is an explicit word-channel interface, discharged separately
from the cited KS07 bound; no startup allowance is assumed. This is separate from the
restricted-source several-source argument. Constructive only; no attacks.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupCommon
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q wordLaw sourceInput)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The current ordinary point resource on the literal original word law. -/
theorem wordLaw_abs_point_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a x : AES.Word) (ha : a ≠ 0) : |wordLaw a x| ≤ 14/q := by
  rw [abs_of_nonneg (AESPaper.StartingWord.wordLaw_nonnegative a x)]
  have h := (raw a x ha).le
  simpa only [wordLaw, q] using h

/-- Reuse the exact common-source Gram expansion with the sharper source
point resource. Every residual leg retains its original source labels. -/
theorem pattern_high_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (b : Fin 4 → Bool) (hb : 2 ≤ residualDegree b)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, action (productProjection (0 : AES.Word) b) (AESPaper.OneSourceLaw.law k a) y ^ 2) ≤
      (14/q)^2 * (300/q)^2 * (2/(15*q))^(residualDegree b-2) *
        (1/(q-1))^(4-residualDegree b) := by
  rw [AESPaper.OneSourceEnergies.pattern_energy b k a ha]
  exact AESPaper.FourSourcePattern.mixed_bound (AESPaper.OneSourceEnergies.G k) (wordLaw a)
    (14/q) (300/q) (2/(15*q)) (1/(q-1))
    (by norm_num [q]) (by norm_num [q]) (by norm_num [q])
    (fun x => wordLaw_abs_point_le raw a x ha)
    (PaperOneSourceGram.source_entry_le k) (PaperOneSourceGram.source_moment_le k) b hb

theorem degree_high_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (j : Fin 5) (hj : 2 ≤ j.val) (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) j (AESPaper.OneSourceLaw.law k a) y ^ 2) ≤
      (Nat.choose 4 j.val : ℝ) * ((14/q)^2 * (300/q)^2 * (2/(15*q))^(j.val-2) *
        (1/(q-1))^(4-j.val)) := by
  apply AESPaper.OneSourceBounds.degree_energy_of_pattern_le
  intro b hb
  have hd : residualDegree b = j.val := congrArg Fin.val hb
  simpa only [hd] using pattern_high_energy_le raw b (by omega) k a ha

/-- The exact physical source count agrees with the adapter's active set. -/
theorem source_count_eq (a : AES.State) :
    AESPaper.ManySourceBounds.activeSourceCount a = (PaperAESStartupSource.active a).card :=
  AESPaper.UniversalInitialization.activeSourceCount_eq_card a

/-- The one-source full-support formula in the actual fourteen-component
profile, after Q^5 scaling. Numerical vector allowances are separate. -/
theorem actual_common_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (hw : (PaperAESStartupSource.active a).card = 1)
    (c : Fin 14) (hi : 2 ≤ SupportProfile.residualDegree c)
    (ht : SupportProfile.supportSize c = 4) :
    (4294967296 : ℝ)^5 *
      (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y ^ 2) ≤
      (PaperStartupScalars.commonSquared (SupportProfile.residualDegree c) : ℚ) := by
  obtain ⟨k, b, hb, hs⟩ := AESPaper.UniversalInitialization.one_active_source a
    (by simpa only [source_count_eq] using hw)
  rw [OneSourceSupport.actual_component_eq_law a k b hs c (by omega)]
  have h := (SupportDegree.component_energy_le_degree (AESPaper.OneSourceLaw.law k b) c).trans
    (degree_high_energy_le raw (SupportDegree.degree c) hi k b hb)
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4294967296^5)
  apply hh.trans
  fin_cases c
  all_goals first
    | (exfalso; revert hi ht; decide)
    | (norm_num [PaperStartupScalars.commonSquared, PaperComparison.q, Nat.choose,
        SupportDegree.degree, SupportProfile.residualDegree, q])

end AES8.PaperAESStartupCommon
