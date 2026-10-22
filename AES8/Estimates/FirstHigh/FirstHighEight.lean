/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.FirstHighNine
import AES8.Estimates.FirstHigh.TwoZeroThirteenMoment
import AES8.Estimates.FirstHigh.TwoZeroTwelveMoment
import AES8.Estimates.FirstHigh.TwoZeroElevenMoment

/-!
# Output-eight assembly from the three projected incoming lengths

The three incoming lengths are proved on the actual two-zero event.
The generic assembly keeps its premises explicit; the final theorem below
instantiates all three from the original-source moment bounds.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace AES8.FirstHighEight
open AESMixing AESMixing.AES
open AES8.SupportProfile (component profile residualDegree)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)
open AES8.FirstHighSupportEvent (boundaryInput)
open AESPaper.GroupedLaw (error)

theorem profile_le_three (f : WordState → ℝ) :
    profile (centeredStep (highPart f)) 8 ≤
      SharpWordNorm.rho ^ 2 * l2 (component (boundaryInput (component f 11)) 8) +
      (SharpWordNorm.rho ^ 2 * l2 (component (boundaryInput (component f 12)) 8) +
       SharpWordNorm.rho ^ 2 * l2 (component (boundaryInput (component f 13)) 8)) := by
  rw [FirstHighNine.highPart_eq_three, TransferAssembly.centeredStep_add,
    TransferAssembly.centeredStep_add]
  apply (TransferAssembly.profile_add_le _ _ (8 : Fin 14)).trans
  apply add_le_add
  · exact FirstHighNine.centered_component_profile_le_projected (component f 11) 8 (by decide)
  · apply (TransferAssembly.profile_add_le _ _ (8 : Fin 14)).trans
    exact add_le_add
      (FirstHighNine.centered_component_profile_le_projected (component f 12) 8 (by decide))
      (FirstHighNine.centered_component_profile_le_projected (component f 13) 8 (by decide))

theorem scalar_eight_le :
    (2 : ℝ)^41 * (SharpWordNorm.rho^2 * (1/1000000) +
      (SharpWordNorm.rho^2 * (1/10000000) + SharpWordNorm.rho^2 * (1/400000))) ≤
        (1000 * g (8 : Fin 14)) * d (8 : Fin 14) := by
  norm_num [SharpWordNorm.rho, g, d, vec14_apply, Fin.ext_iff]

/-- Exactly two explicit incoming-length premises; incoming13 is instantiated. -/
theorem firstHigh_eight_of_projected_lengths (b : AES.State) (hb : b ≠ 0)
    (h11 : (2 : ℝ)^80 * l2 (component
      (boundaryInput (component (error 1 b) 11)) 8) ≤ 1/1000000)
    (h12 : (2 : ℝ)^80 * l2 (component
      (boundaryInput (component (error 1 b) 12)) 8) ≤ 1/10000000) :
    profile (centeredStep (highPart (error 1 b))) 8 ≤
      (d (8 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (8 : Fin 14)) := by
  have h13 := TwoZeroThirteenMoment.actual_projected_eight_scaled_length_le b hb
  have hscaled : (2 : ℝ)^80 * profile (centeredStep (highPart (error 1 b))) 8 ≤
      SharpWordNorm.rho^2 * (1/1000000) + (SharpWordNorm.rho^2 * (1/10000000) +
        SharpWordNorm.rho^2 * (1/400000)) := by
    calc
      _ ≤ (2 : ℝ)^80 * (SharpWordNorm.rho^2 *
          l2 (component (boundaryInput (component (error 1 b) 11)) 8) +
          (SharpWordNorm.rho^2 * l2 (component (boundaryInput (component (error 1 b) 12)) 8) +
           SharpWordNorm.rho^2 * l2 (component (boundaryInput (component (error 1 b) 13)) 8))) :=
        mul_le_mul_of_nonneg_left (profile_le_three (error 1 b)) (by positivity)
      _ = SharpWordNorm.rho^2 * ((2 : ℝ)^80 *
          l2 (component (boundaryInput (component (error 1 b) 11)) 8)) +
          (SharpWordNorm.rho^2 * ((2 : ℝ)^80 *
            l2 (component (boundaryInput (component (error 1 b) 12)) 8)) +
           SharpWordNorm.rho^2 * ((2 : ℝ)^80 *
            l2 (component (boundaryInput (component (error 1 b) 13)) 8))) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h11 (sq_nonneg _))
        (add_le_add (mul_le_mul_of_nonneg_left h12 (sq_nonneg _))
          (mul_le_mul_of_nonneg_left h13 (sq_nonneg _)))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ)^41 * (2 : ℝ)^80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have ht : NormalizedProfile.factor 1 *
      profile (centeredStep (highPart (error 1 b))) 8 ≤
        (1000 * g (8 : Fin 14)) * d (8 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans scalar_eight_le
  calc
    _ ≤ ((1000 * g (8 : Fin 14)) * d (8 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

/-- Universal first-high output eight, with all incoming length bounds proved. -/
theorem firstHigh_eight (b : AES.State) (hb : b ≠ 0) :
    profile (centeredStep (highPart (error 1 b))) 8 ≤
      (d (8 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (8 : Fin 14)) :=
  firstHigh_eight_of_projected_lengths b hb
    (TwoZeroElevenMoment.actual_projected_eight_scaled_length_le b hb)
    (TwoZeroTwelveMoment.actual_projected_eight_scaled_length_le b hb)

end AES8.FirstHighEight
