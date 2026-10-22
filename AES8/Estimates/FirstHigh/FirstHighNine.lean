/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighSupportEvent

/-!
# Fixed output-nine assembly from the actual projected-boundary moment

This module isolates the quantitative moment still needed for output nine.
The incoming eleven and twelve lengths are bounded universally by 11/1000
and 33/500. These slightly relaxed allowances avoid source-count branches in
the final assembly, while preserving a positive exact scalar margin.
All source-count reasoning occurs on the actual initial source laws.
No missing moment is assumed as a global axiom or inferred from a paper claim.
Constructive proof work only; no attacks or manuscript/predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.FirstHighNine
open AESMixing AESMixing.AES AESConcrete
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AES8.SupportProfile (component profile residualDegree)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)
open AES8.FirstHighSupportEvent (boundaryInput)

def a11 : ℝ := AESRound.Terminal.lambda * AESRound.Certificate.L 9 11
def a12 : ℝ := AESRound.Terminal.lambda * AESRound.Certificate.L 9 12

theorem eleven_scaled_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ)^80 * profile (error 1 b) 11 ≤ 11/1000 := by
  by_cases h : activeSourceCount b = 1
  · rw [OneSourceSupport.actual_profile_eleven_eq_zero b h, mul_zero]
    norm_num
  · have hp := AESPaper.UniversalInitialization.activeSourceCount_pos b hb
    exact FirstHighSeveralSource.high_component_scaled_le b (by omega) (0 : Fin 3)

theorem twelve_scaled_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ)^80 * profile (error 1 b) 12 ≤ 33/500 := by
  by_cases h : activeSourceCount b = 1
  · exact (FirstHighTwelve.component_twelve_scaled_le b h).trans
      (by norm_num [FirstHighTwelve.b3])
  · have hp := AESPaper.UniversalInitialization.activeSourceCount_pos b hb
    have hm := FirstHighSeveralSource.high_component_scaled_le b (by omega) (1 : Fin 3)
    exact hm.trans (by norm_num [FirstHighSeveralSource.highBudget])

/-- Retain the actual target projection before the residual channel damping. -/
theorem centered_component_profile_le_projected (f : WordState → ℝ) (c : Fin 14)
    (hc : LegacyProjection.residualIndex c ≠ 0) :
    profile (centeredStep f) c ≤ SharpWordNorm.rho ^ residualDegree c *
      l2 (component (boundaryInput f) c) := by
  have he : (∑ y, component (centeredStep f) c y ^ 2) ≤
      (SharpWordNorm.rho ^ residualDegree c) ^ 2 *
        ∑ y, component (boundaryInput f) c y ^ 2 := by
    rw [FirstHighSupportEvent.centered_component_eq_channel f c hc]
    simp_rw [LegacyProjection.component_eq_refinedKernel_action]
    simpa only [LegacyProjection.residualIndex_val, AES.parallelSuperboxKernel] using
      (RefinedChannelCommutation.refined_damped_energy AES.wordSuperboxKernel
        (0 : AES.Word) SupportProfile.word_card_gt_one AES.word_superbox_pointed
        SharpWordNorm.rho SharpDegreeStep.word_superbox_residual_energy
        (LegacyProjection.residualIndex c) (LegacyProjection.activeIndex c)
        (boundaryInput f))
  exact l2_le_of_energy _ _ (SharpWordNorm.rho ^ residualDegree c)
    (pow_nonneg (by norm_num [SharpWordNorm.rho]) _) he

theorem highPart_eq_three (f : WordState → ℝ) :
    highPart f = component f 11 + (component f 12 + component f 13) := by
  funext x
  simp only [highPart, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.add_apply]
  rfl

theorem profile_le_three (f : WordState → ℝ) :
    profile (centeredStep (highPart f)) 9 ≤
      a11 * profile f 11 + (a12 * profile f 12 +
        SharpWordNorm.rho^2 * l2 (component (boundaryInput (component f 13)) 9)) := by
  rw [highPart_eq_three, TransferAssembly.centeredStep_add,
    TransferAssembly.centeredStep_add]
  apply (TransferAssembly.profile_add_le _ _ (9 : Fin 14)).trans
  apply add_le_add
  · exact LegacyTransfer.profile_le_of_operator_cap f 9 11
      (FirstHighSeveralSource.old_operator_cap 9 11)
  · apply (TransferAssembly.profile_add_le _ _ (9 : Fin 14)).trans
    exact add_le_add
      (LegacyTransfer.profile_le_of_operator_cap f 9 12
        (FirstHighSeveralSource.old_operator_cap 9 12))
      (centered_component_profile_le_projected (component f 13) 9 (by decide))

theorem projected_length_le (b : AES.State)
    (hmoment : AESPaper.StartingWord.q ^ 5 *
      (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) ≤
        (49 : ℝ) / 10000000000) :
    (2 : ℝ)^80 * l2 (component (boundaryInput (component (error 1 b) 13)) 9) ≤
      7/100000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ)^80)^2 = AESPaper.StartingWord.q^5 := by
    norm_num [AESPaper.StartingWord.q]
  rw [hs]
  exact hmoment.trans (by norm_num)

theorem scalar_nine_le :
    (2 : ℝ)^41 * (a11 * (11/1000) +
      (a12 * (33/500) + SharpWordNorm.rho^2 * (7/100000))) ≤
        (1000 * g (9 : Fin 14)) * d (9 : Fin 14) := by
  norm_num [a11, a12, SharpWordNorm.rho, AESRound.Terminal.lambda,
    AESRound.Certificate.L, g, d, vec14_apply, Fin.ext_iff]

/-- The only unproved premise here is the explicitly stated actual moment. -/
theorem firstHigh_nine_of_projected_boundary_moment (b : AES.State) (hb : b ≠ 0)
    (hmoment : AESPaper.StartingWord.q ^ 5 *
      (∑ y, component (boundaryInput (component (error 1 b) 13)) 9 y ^ 2) ≤
        (49 : ℝ) / 10000000000) :
    profile (centeredStep (highPart (error 1 b))) 9 ≤
      (d (9 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (9 : Fin 14)) := by
  have hscaled : (2 : ℝ)^80 * profile (centeredStep (highPart (error 1 b))) 9 ≤
      a11 * (11/1000) + (a12 * (33/500) + SharpWordNorm.rho^2 * (7/100000)) := by
    calc
      _ ≤ (2 : ℝ)^80 * (a11 * profile (error 1 b) 11 +
          (a12 * profile (error 1 b) 12 + SharpWordNorm.rho^2 *
            l2 (component (boundaryInput (component (error 1 b) 13)) 9))) :=
        mul_le_mul_of_nonneg_left (profile_le_three (error 1 b)) (by positivity)
      _ = a11 * ((2 : ℝ)^80 * profile (error 1 b) 11) +
          (a12 * ((2 : ℝ)^80 * profile (error 1 b) 12) + SharpWordNorm.rho^2 *
            ((2 : ℝ)^80 * l2 (component (boundaryInput (component (error 1 b) 13)) 9))) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (eleven_scaled_le b hb)
          (FirstHighSeveralSource.old_coefficient_nonneg 9 11))
        (add_le_add
          (mul_le_mul_of_nonneg_left (twelve_scaled_le b hb)
            (FirstHighSeveralSource.old_coefficient_nonneg 9 12))
          (mul_le_mul_of_nonneg_left (projected_length_le b hmoment) (sq_nonneg _)))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ)^41 * (2 : ℝ)^80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have ht : NormalizedProfile.factor 1 *
      profile (centeredStep (highPart (error 1 b))) 9 ≤
        (1000 * g (9 : Fin 14)) * d (9 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_nine_le
  calc
    _ ≤ ((1000 * g (9 : Fin 14)) * d (9 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

end AES8.FirstHighNine
