import AES8.Reductions.Source.PaperAESSourceLaw
import AES8.Reductions.Source.PaperAESSourceMDS

/-!
# Current-paper zero-event theorems on the literal AES source

These applications use the generic `lem:marginals` proof, the independently
checked AES diffusion criterion, and the actual byte laws. No legacy table
of shortened-source probability caps, desired event bound, or energy bound
is supplied as a hypothesis. All probabilities remain unnormalized joint
events of the original independent source.

The ordinary/inverse diffusion directions covered here are the literal
`byteDiffusionHom inverse`. Transpose/Fourier word-operator correspondence,
positive residual-degree recombination, and the full mixing theorem are
separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Word inputColumn)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open PaperRestrictedDiffusion

attribute [local instance] Classical.propDecidable

/-- The complete two-branch bound of `lem:marginals` (a), including the
impossible case, on the concrete AES law and any further input indicator. -/
theorem specified_zero_mass_le (right : Orientation) (inverse : Bool) (a : Word)
    (ha : a ≠ 0) (r : Fin 16) (event : Word → Prop) :
    (∑ x : Word, if AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x ∧ event x
      then inputColumn right a x else 0) ≤
      zeroEventBound (active a).card (maskSize r) (1 / 64) (65 / 8192) := by
  rw [← eventMass_eq_concrete right inverse a r event, ← maskSet_card r]
  exact paper_zero_event_mass_bound (byteDiffusionHom inverse)
    (byteDiffusion_graph_isMDS inverse) (active a) (maskSet r) (active_nonempty a ha)
    (law right a) event (1 / 64) (65 / 8192) (by norm_num) (by norm_num)
    (fun i _ x => law_nonneg right a i x) (fun i _ => law_mass_one right a i)
    (fun i hi x => law_point_le right a i hi x)
    (fun i hi => (law_collision right a i hi).le) (fun i hi => law_zero right a i hi)

/-- Every nonempty exact output-zero event has the paper's simple cap,
derived through the current generic route rather than the legacy cap table. -/
theorem exact_zero_mass_le (right : Orientation) (inverse : Bool) (a : Word)
    (ha : a ≠ 0) (r : Fin 16) (hr : 0 < maskSize r) :
    AESConcrete.ActualZeroEventProbabilities.exactMass right inverse a r ≤
      (1 / 64 : ℝ) ^ (maskSize r - 1) * (65 / 8192) := by
  rw [← exactMass_eq_concrete right inverse a r, ← maskSet_card r]
  obtain ⟨i, hi⟩ := active_nonempty a ha
  exact PaperSourceZeroEvents.exactMass_le_cap (byteDiffusionHom inverse)
    (byteDiffusion_graph_isMDS inverse) (active a) (maskSet r) (by simpa using hr)
    (law right a) (1 / 64) (65 / 8192) (by norm_num) (by norm_num)
    (fun i _ x => law_nonneg right a i x) (fun i _ => law_mass_one right a i)
    (fun i hi x => law_point_le right a i hi x)
    (fun i hi => (law_collision right a i hi).le) ⟨i, hi, law_zero right a i hi⟩

/-- Reindex the complete sixteen-event collision quadratic exactly. -/
theorem probability_collision_eq_generic (right : Orientation) (inverse : Bool) (a : Word)
    (Q : ℝ) :
    (∑ r : Fin 16, Q ^ maskSize r *
      AESConcrete.ActualZeroEventProbabilities.exactMass right inverse a r ^ 2) =
      ∑ z : Finset (Fin 4), Q ^ z.card *
        PaperSourceZeroEvents.exactMass (byteDiffusionHom inverse) (active a)
          (law right a) z ^ 2 := by
  rw [← maskSetEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  change _ = Q ^ (maskSet r).card *
    PaperSourceZeroEvents.exactMass (byteDiffusionHom inverse) (active a)
      (law right a) (maskSet r) ^ 2
  rw [maskSet_card, exactMass_eq_concrete]

/-- The current generic all-caps theorem now applies to actual AES mask
probabilities. The right side is symbolic, with no numerical evaluation. -/
theorem probability_collision_le_generic_majorant (right : Orientation) (inverse : Bool)
    (a : Word) (ha : a ≠ 0) :
    (∑ r : Fin 16, (255 : ℝ) ^ maskSize r *
      AESConcrete.ActualZeroEventProbabilities.exactMass right inverse a r ^ 2) ≤
      PaperSourceMajorization.quadratic
        (fun z : PaperSourceZeroEvents.ProperZeros (Fin 4) => (255 : ℝ) ^ z.val.card)
        (fun z : PaperSourceZeroEvents.ProperZeros (Fin 4) =>
          (1 / 64 : ℝ) ^ (z.val.card - 1) * (65 / 8192)) := by
  rw [probability_collision_eq_generic]
  obtain ⟨i, hi⟩ := active_nonempty a ha
  exact PaperSourceZeroEvents.actual_source_collision_le (byteDiffusionHom inverse)
    (byteDiffusion_graph_isMDS inverse) (active a) (law right a) 255 (1 / 64) (65 / 8192)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i _ x => law_nonneg right a i x) (fun i _ => law_mass_one right a i)
    (fun i hi x => law_point_le right a i hi x)
    (fun i hi => (law_collision right a i hi).le) ⟨i, hi, law_zero right a i hi⟩
    (by norm_num) (by norm_num)

end AES8.PaperAESSource
