/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Source.SharpOneSourceLengths
import AES8.Estimates.Transfer.SharpDegreeStep
import AES8.Reductions.Source.OneSourceSupport
import AES8.Estimates.FirstHigh.FirstHighSeveralSource

/-!
# Close first-high coordinate twelve for every nonzero source

The one-source support identity removes component eleven. For the remaining
two components, retain the unrounded inherited source energies and the newly
proved word norm. The exact scalar margin is positive; no target estimate is
assumed. The several-source case reuses its existing proved bound.
Constructive proof work only; no manuscript or predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.FirstHighTwelve
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AES8.SupportProfile (profile component)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)

def b3 : ℝ := 659321008722873 / 10000000000000000
def b4 : ℝ := 30093749063103 / 2500000000000000
def alpha : ℝ := AESRound.Terminal.lambda * AESRound.Certificate.L 12 12

theorem component_twelve_scaled_le (a : AES.State) (ha : activeSourceCount a = 1) :
    (2 : ℝ)^80 * profile (error 1 a) 12 ≤ b3 := by
  have hr := SupportDegree.profile_le_degree (error 1 a) (12 : Fin 14)
  change profile (error 1 a) 12 ≤
    l2 (degreeComponent (0 : AES.Word) 3 (error 1 a)) at hr
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
    (SharpOneSourceLengths.scaled_degree_three_le a ha)

theorem component_thirteen_scaled_le (a : AES.State) (ha : activeSourceCount a = 1) :
    (2 : ℝ)^80 * profile (error 1 a) 13 ≤ b4 := by
  have hr := SupportDegree.profile_le_degree (error 1 a) (13 : Fin 14)
  change profile (error 1 a) 13 ≤
    l2 (degreeComponent (0 : AES.Word) 4 (error 1 a)) at hr
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
    (SharpOneSourceLengths.scaled_degree_four_le a ha)

theorem one_source_profile_le (a : AES.State) (ha : activeSourceCount a = 1) :
    profile (centeredStep (highPart (error 1 a))) 12 ≤
      alpha * profile (error 1 a) 12 +
        SharpWordNorm.rho^3 * profile (error 1 a) 13 := by
  rw [OneSourceSupport.actual_highPart_eq_two a ha, TransferAssembly.centeredStep_add]
  exact (TransferAssembly.profile_add_le _ _ (12 : Fin 14)).trans
    (add_le_add
      (LegacyTransfer.profile_le_of_operator_cap (error 1 a) 12 12
        (FirstHighSeveralSource.old_operator_cap 12 12))
      (LegacyTransfer.profile_le_of_operator_cap (error 1 a) 12 13
        SharpDegreeStep.twelve_thirteen_operator_cap))

theorem scalar_le :
    (2 : ℝ)^41 * (alpha * b3 + SharpWordNorm.rho^3 * b4) ≤
      (1000 * g (12 : Fin 14)) * d (12 : Fin 14) := by
  norm_num [alpha, b3, b4, SharpWordNorm.rho, AESRound.Terminal.lambda,
    AESRound.Certificate.L, g, d, vec14_apply, Fin.ext_iff]

theorem firstHigh_twelve_of_one (a : AES.State) (ha : activeSourceCount a = 1) :
    profile (centeredStep (highPart (error 1 a))) 12 ≤
      (d (12 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (12 : Fin 14)) := by
  have hscaled : (2 : ℝ)^80 * profile (centeredStep (highPart (error 1 a))) 12 ≤
      alpha * b3 + SharpWordNorm.rho^3 * b4 := by
    calc
      _ ≤ (2 : ℝ)^80 * (alpha * profile (error 1 a) 12 +
          SharpWordNorm.rho^3 * profile (error 1 a) 13) :=
        mul_le_mul_of_nonneg_left (one_source_profile_le a ha) (by positivity)
      _ = alpha * ((2 : ℝ)^80 * profile (error 1 a) 12) +
          SharpWordNorm.rho^3 * ((2 : ℝ)^80 * profile (error 1 a) 13) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (component_twelve_scaled_le a ha)
          (FirstHighSeveralSource.old_coefficient_nonneg 12 12))
        (mul_le_mul_of_nonneg_left (component_thirteen_scaled_le a ha)
          (by norm_num [SharpWordNorm.rho]))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ)^41 * (2 : ℝ)^80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have hb : NormalizedProfile.factor 1 *
      profile (centeredStep (highPart (error 1 a))) 12 ≤
        (1000 * g (12 : Fin 14)) * d (12 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_le
  calc
    _ ≤ ((1000 * g (12 : Fin 14)) * d (12 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using hb
    _ = _ := by ring

/-- Complete coordinate-twelve bound for the actual nonzero-source error. -/
theorem firstHigh_twelve (a : AES.State) (ha : a ≠ 0) :
    profile (centeredStep (highPart (error 1 a))) 12 ≤
      (d (12 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (12 : Fin 14)) := by
  by_cases h1 : activeSourceCount a = 1
  · exact firstHigh_twelve_of_one a h1
  · have hp := AESPaper.UniversalInitialization.activeSourceCount_pos a ha
    exact FirstHighSeveralSource.firstHigh_twelve_of_several a (by omega)

end AES8.FirstHighTwelve
