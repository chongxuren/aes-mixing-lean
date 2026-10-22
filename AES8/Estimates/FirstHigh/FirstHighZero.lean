/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.ActualZeroMoment

/-!
# Coordinate-zero assembly with input-side centering

Output zero has residual degree zero. Its uniform correction is removed on
each positive-degree INPUT, using both value-at-zero and total-mass identities.
The signed actual boundary masses then control the two remaining lengths.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.FirstHighZero
open AESMixing AESMixing.AES AESConcrete
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component profile residualDegree)
open AES8.FirstHighSupportEvent (boundaryInput)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)

/-- Centering is justified by the input; the output degree is unrestricted. -/
theorem centered_input_component_eq_channel (f : WordState → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) (c : Fin 14) :
    component (centeredStep f) c =
      action AES.parallelSuperboxKernel (component (boundaryInput f) c) := by
  have hstep : centeredStep f = action WordStepZeros.wordStepKernel f := by
    unfold centeredStep
    rw [kernel_action_sub,
      DegreeCentering.globalUniformKernel_action_eq_zero (0 : AES.Word) f (by exact hz) hs,
      sub_zero]
  rw [hstep, LegacyProjection.component_eq_refinedKernel_action,
    WordStepZeros.wordStepKernel_action]
  change action
      (RefinedWordProjection.refinedKernel (0 : AES.Word)
        (LegacyProjection.residualIndex c) (LegacyProjection.activeIndex c))
      (action (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel))
        (boundaryInput f)) = _
  rw [← kernelCompose_action,
    RefinedChannelCommutation.refined_channel_commutes AES.wordSuperboxKernel
      (0 : AES.Word) AES.word_superbox_pointed
      (LegacyProjection.residualIndex c) (LegacyProjection.activeIndex c),
    kernelCompose_action]
  rw [← LegacyProjection.component_eq_refinedKernel_action (boundaryInput f) c]
  rfl

/-- The degree-zero case retains channel norm one after input-side centering. -/
theorem centered_input_profile_le_projected (f : WordState → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) (c : Fin 14) :
    profile (centeredStep f) c ≤ SharpWordNorm.rho ^ residualDegree c *
      l2 (component (boundaryInput f) c) := by
  have he : (∑ y, component (centeredStep f) c y ^ 2) ≤
      (SharpWordNorm.rho ^ residualDegree c) ^ 2 *
        ∑ y, component (boundaryInput f) c y ^ 2 := by
    rw [centered_input_component_eq_channel f hz hs c]
    simp_rw [LegacyProjection.component_eq_refinedKernel_action]
    simpa only [LegacyProjection.residualIndex_val, AES.parallelSuperboxKernel] using
      (RefinedChannelCommutation.refined_damped_energy AES.wordSuperboxKernel
        (0 : AES.Word) SupportProfile.word_card_gt_one AES.word_superbox_pointed
        SharpWordNorm.rho SharpDegreeStep.word_superbox_residual_energy
        (LegacyProjection.residualIndex c) (LegacyProjection.activeIndex c)
        (boundaryInput f))
  exact l2_le_of_energy _ _ (SharpWordNorm.rho ^ residualDegree c)
    (pow_nonneg (by norm_num [SharpWordNorm.rho]) _) he

theorem positive_component_mass (f : WordState → ℝ) (j : Fin 14)
    (hj : SupportDegree.degree j ≠ 0) : (∑ x, component f j x) = 0 := by
  have hm := DegreeCentering.degreeComponent_sum_zero
    (0 : AES.Word) SupportProfile.word_card_gt_one (SupportDegree.degree j) hj
    (component f j)
  rw [TransferZeros.degree_component] at hm
  exact hm

/-- A positive input component supplies the two centering hypotheses exactly. -/
theorem positive_component_profile_le_projected (f : WordState → ℝ) (j : Fin 14)
    (hj : SupportDegree.degree j ≠ 0) (c : Fin 14) :
    profile (centeredStep (component f j)) c ≤ SharpWordNorm.rho ^ residualDegree c *
      l2 (component (boundaryInput (component f j)) c) :=
  centered_input_profile_le_projected (component f j)
    (SupportProfile.component_at_zero f j) (positive_component_mass f j hj) c

/-- This exact zero comes from the admitted old operator table. -/
theorem incoming_eleven_profile_le_zero (f : WordState → ℝ) :
    profile (centeredStep (component f 11)) 0 ≤ 0 := by
  have h := LegacyTransfer.profile_le_of_operator_cap f 0 11
    (FirstHighSeveralSource.old_operator_cap 0 11)
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L] at h
  exact h

theorem profile_le_two (f : WordState → ℝ) :
    profile (centeredStep (highPart f)) 0 ≤
      l2 (component (boundaryInput (component f 12)) 0) +
      l2 (component (boundaryInput (component f 13)) 0) := by
  rw [FirstHighNine.highPart_eq_three, TransferAssembly.centeredStep_add,
    TransferAssembly.centeredStep_add]
  have h12 := positive_component_profile_le_projected f 12 (by decide) 0
  have h13 := positive_component_profile_le_projected f 13 (by decide) 0
  change profile (centeredStep (component f 12)) 0 ≤
    SharpWordNorm.rho ^ 0 * l2 (component (boundaryInput (component f 12)) 0) at h12
  change profile (centeredStep (component f 13)) 0 ≤
    SharpWordNorm.rho ^ 0 * l2 (component (boundaryInput (component f 13)) 0) at h13
  simp only [pow_zero, _root_.one_mul] at h12 h13
  calc
    _ ≤ profile (centeredStep (component f 11)) 0 +
        (profile (centeredStep (component f 12)) 0 + profile (centeredStep (component f 13)) 0) :=
      (TransferAssembly.profile_add_le _ _ 0).trans
        (add_le_add le_rfl (TransferAssembly.profile_add_le _ _ 0))
    _ ≤ 0 + (l2 (component (boundaryInput (component f 12)) 0) +
        l2 (component (boundaryInput (component f 13)) 0)) :=
      add_le_add (incoming_eleven_profile_le_zero f) (add_le_add h12 h13)
    _ = _ := zero_add _

theorem scalar_zero_le :
    (2 : ℝ) ^ 41 * ((1 / 100000000000) + (1 / 100000000000)) ≤
      (1000 * g (0 : Fin 14)) * d (0 : Fin 14) := by
  norm_num [g, d, vec14_apply, Fin.ext_iff]

/-- Candidate for one first-high coordinate, universally over nonzero b.
The other coordinates and the complete physical-cap endpoint remain separate. -/
theorem firstHigh_zero (b : AES.State) (hb : b ≠ 0) :
    profile (centeredStep (highPart (error 1 b))) 0 ≤
      (d (0 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (0 : Fin 14)) := by
  have hscaled : (2 : ℝ) ^ 80 * profile (centeredStep (highPart (error 1 b))) 0 ≤
      (1 / 100000000000) + (1 / 100000000000) := by
    calc
      _ ≤ (2 : ℝ) ^ 80 *
          (l2 (component (boundaryInput (component (error 1 b) 12)) 0) +
            l2 (component (boundaryInput (component (error 1 b) 13)) 0)) :=
        mul_le_mul_of_nonneg_left (profile_le_two (error 1 b)) (by positivity)
      _ = (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 12)) 0) +
          (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 13)) 0) := by ring
      _ ≤ _ := add_le_add (ActualZeroMoment.actual_twelve_projected_length_le b hb)
        (ActualZeroMoment.actual_thirteen_projected_length_le b hb)
  have hn : NormalizedProfile.factor 1 = (2 : ℝ) ^ 41 * (2 : ℝ) ^ 80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have ht : NormalizedProfile.factor 1 * profile (centeredStep (highPart (error 1 b))) 0 ≤
      (1000 * g (0 : Fin 14)) * d (0 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_zero_le
  calc
    _ ≤ ((1000 * g (0 : Fin 14)) * d (0 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

end AES8.FirstHighZero
