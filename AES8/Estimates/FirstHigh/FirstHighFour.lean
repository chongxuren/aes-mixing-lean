/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.ActualFourMoment

/-! Coordinate-four assembly. The actual moment module supplies both
nonzero incoming lengths; the admitted old zero block supplies incoming eleven.
No analytic premise remains in the final theorem.  -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

namespace AES8.FirstHighFour
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component profile)
open AES8.FirstHighSupportEvent (boundaryInput)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)

/-- The exact admitted cap is zero. Keep this source dependency visible. -/
theorem incoming_eleven_profile_le_zero (f : WordState → ℝ) :
    profile (centeredStep (component f 11)) 4 ≤ 0 := by
  have h := LegacyTransfer.profile_le_of_operator_cap f 4 11
    (FirstHighSeveralSource.old_operator_cap 4 11)
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L] at h
  exact h

theorem profile_le_two (f : WordState → ℝ) :
    profile (centeredStep (highPart f)) 4 ≤
      SharpWordNorm.rho * l2 (component (boundaryInput (component f 12)) 4) +
      SharpWordNorm.rho * l2 (component (boundaryInput (component f 13)) 4) := by
  rw [FirstHighNine.highPart_eq_three, TransferAssembly.centeredStep_add,
    TransferAssembly.centeredStep_add]
  have h12 := FirstHighNine.centered_component_profile_le_projected (component f 12) 4 (by decide)
  have h13 := FirstHighNine.centered_component_profile_le_projected (component f 13) 4 (by decide)
  change profile (centeredStep (component f 12)) 4 ≤
    SharpWordNorm.rho ^ 1 * l2 (component (boundaryInput (component f 12)) 4) at h12
  change profile (centeredStep (component f 13)) 4 ≤
    SharpWordNorm.rho ^ 1 * l2 (component (boundaryInput (component f 13)) 4) at h13
  simp only [pow_one] at h12 h13
  calc
    _ ≤ profile (centeredStep (component f 11)) 4 +
        (profile (centeredStep (component f 12)) 4 + profile (centeredStep (component f 13)) 4) :=
      (TransferAssembly.profile_add_le _ _ 4).trans
        (add_le_add le_rfl (TransferAssembly.profile_add_le _ _ 4))
    _ ≤ 0 + (SharpWordNorm.rho * l2 (component (boundaryInput (component f 12)) 4) +
        SharpWordNorm.rho * l2 (component (boundaryInput (component f 13)) 4)) :=
      add_le_add (incoming_eleven_profile_le_zero f) (add_le_add h12 h13)
    _ = _ := zero_add _

theorem scalar_four_le :
    (2 : ℝ) ^ 41 * (SharpWordNorm.rho * (1 / 1000000000) +
      SharpWordNorm.rho * (1 / 500000000)) ≤ (1000 * g (4 : Fin 14)) * d (4 : Fin 14) := by
  norm_num [SharpWordNorm.rho, g, d, vec14_apply, Fin.ext_iff]

/-- Universal candidate for one remaining first-high coordinate. It does not
provide the other eight coordinates or a RemainingCaps/global endpoint proof. -/
theorem firstHigh_four (b : AES.State) (hb : b ≠ 0) :
    profile (centeredStep (highPart (error 1 b))) 4 ≤
      (d (4 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (4 : Fin 14)) := by
  have hscaled : (2 : ℝ) ^ 80 * profile (centeredStep (highPart (error 1 b))) 4 ≤
      SharpWordNorm.rho * (1 / 1000000000) + SharpWordNorm.rho * (1 / 500000000) := by
    calc
      _ ≤ (2 : ℝ) ^ 80 *
          (SharpWordNorm.rho * l2 (component (boundaryInput (component (error 1 b) 12)) 4) +
          SharpWordNorm.rho * l2 (component (boundaryInput (component (error 1 b) 13)) 4)) :=
        mul_le_mul_of_nonneg_left (profile_le_two (error 1 b)) (by positivity)
      _ = SharpWordNorm.rho * ((2 : ℝ) ^ 80 *
          l2 (component (boundaryInput (component (error 1 b) 12)) 4)) +
          SharpWordNorm.rho * ((2 : ℝ) ^ 80 *
          l2 (component (boundaryInput (component (error 1 b) 13)) 4)) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (ActualFourMoment.actual_twelve_projected_length_le b hb)
          (by norm_num [SharpWordNorm.rho]))
        (mul_le_mul_of_nonneg_left (ActualFourMoment.actual_thirteen_projected_length_le b hb)
          (by norm_num [SharpWordNorm.rho]))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ) ^ 41 * (2 : ℝ) ^ 80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have ht : NormalizedProfile.factor 1 * profile (centeredStep (highPart (error 1 b))) 4 ≤
      (1000 * g (4 : Fin 14)) * d (4 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_four_le
  calc
    _ ≤ ((1000 * g (4 : Fin 14)) * d (4 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

end AES8.FirstHighFour
