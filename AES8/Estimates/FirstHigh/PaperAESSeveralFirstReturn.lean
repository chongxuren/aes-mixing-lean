import AES8.Reductions.Source.PaperAESTwoRoundProfile
import AES8.Estimates.Transfer.PaperAESCurrentReturn
import AESPaper.SeveralSourcePositiveProfile

/-! The physical first-return estimate for two, three or four active sources.
The return operator and current comparison matrix are literal AES objects.
Only the all-bit mixed-entry resource remains a hypothesis. The initial source
is kept uncentered after proving exact cancellation of the stationary term. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSeveralFirstReturn
open AESMixing PaperComparison TransferAssembly SupportEvolution
open PaperAESTwoRoundSource PaperAESTwoRoundProfile
open AESPaper.GroupedLaw (error groupedLaw)
open AESPaper.GroupedRecurrence (step)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem highPart_uniform : highPart (uniformExcept (0 : AES.WordState)) = 0 := by
  rw [HighDegreeIdentity.highPart_eq_degrees,
    AESPaper.SeveralSourcePositiveProfile.uniform_positive_degree 3 (by decide),
    AESPaper.SeveralSourcePositiveProfile.uniform_positive_degree 4 (by decide), add_zero]

theorem firstHigh_eq_source_return (a : AES.State) :
    centeredStep (highPart (error 1 a)) = highReturn (groupedLaw 0 a) := by
  rw [centeredStep_high_eq_step, AESPaper.GroupedRecurrence.error_step 0 a,
    AESPaper.GroupedRecurrence.error_eq_sub, AESPaper.GroupedRecurrence.step_sub,
    AESPaper.GroupedRecurrence.step_uniform, ReturnCentering.highPart_sub,
    highPart_uniform, sub_zero, ReturnCentering.highReturn_eq_uncentered]

theorem source_zero (a : AES.State) (ha : a ≠ 0) : groupedLaw 0 a 0 = 0 := by
  have h := AESPaper.GroupedLaw.error_zero 0 a ha
  simpa only [error, uniformExcept, if_true, sub_zero] using h

theorem return_profile_le (f : AES.WordState → ℝ) (hz : f 0 = 0)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (i : Fin 14) :
    SupportProfile.profile (highReturn f) i ≤
      ∑ k : Fin 14, physicalCoeff 2 i k (realReturn i k) * SupportProfile.profile f k := by
  have he : highReturn f =
      fun x => ∑ k : Fin 14, highReturn (SupportProfile.component f k) x := by
    calc
      _ = highReturn (fun x => ∑ k : Fin 14, SupportProfile.component f k x) :=
        congrArg highReturn (funext fun x => (SupportProfile.component_decomposition f hz x).symm)
      _ = _ := highReturn_sum _
  rw [he]
  exact (profile_sum_le _ i).trans (Finset.sum_le_sum
    (fun k _ => PaperAESCurrentReturn.high_cap f i k hentry))

theorem normalization (f : AES.WordState → ℝ) (i : Fin 14) :
    (NormalizedProfile.factor 1 / (1000 * d i)) *
      (∑ k : Fin 14, physicalCoeff 2 i k (realReturn i k) * SupportProfile.profile f k) =
    ∑ k : Fin 14, realReturn i k *
      ((omega41 * (2 : ℝ)^80 / (1000 * d k)) * SupportProfile.profile f k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold physicalCoeff NormalizedProfile.factor
  simp only [pow_one]
  field_simp [(NormalizedProfile.diagonal_pos i).ne',
    (NormalizedProfile.diagonal_pos k).ne', omega41_pos.ne']
  <;> ring

/-- Actual several-source first-high remainder, in the exact PhysicalCaps units. -/
theorem firstHigh_le (a : AES.State) (ha : a ≠ 0)
    (hw : 2 ≤ PaperSupportProjection.supportCount (sourceMask a))
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (i : Fin 14) :
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * (firstReturn i : ℝ)) := by
  have hc : 0 < NormalizedProfile.factor 1 / (1000 * d i) :=
    div_pos (NormalizedProfile.factor_pos _) (mul_pos (by norm_num) (NormalizedProfile.diagonal_pos i))
  apply le_of_mul_le_mul_left (a := NormalizedProfile.factor 1 / (1000 * d i)) ?_ hc
  rw [firstHigh_eq_source_return]
  calc
    _ ≤ (NormalizedProfile.factor 1 / (1000 * d i)) *
        (∑ k : Fin 14, physicalCoeff 2 i k (realReturn i k) *
          SupportProfile.profile (groupedLaw 0 a) k) :=
      mul_le_mul_of_nonneg_left (return_profile_le _ (source_zero a ha) hentry i) hc.le
    _ = _ := normalization _ i
    _ ≤ ∑ k : Fin 14, realReturn i k *
        (PaperFirstReturnComparison.severalSource k : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (several_scaled_profile_le a hw k) (realReturn_nonneg i k)
    _ ≤ (firstReturn i : ℝ) := by
      have h := PaperFirstReturnComparison.several_source_le i
      unfold mv at h
      unfold realReturn
      exact_mod_cast h
    _ = _ := by
      field_simp [(NormalizedProfile.diagonal_pos i).ne', (NormalizedProfile.factor_pos 1).ne']

end AES8.PaperAESSeveralFirstReturn
