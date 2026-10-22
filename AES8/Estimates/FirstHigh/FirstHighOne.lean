/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.ActualOneMoment

/-! Coordinate-one first-high assembly. All three positive-degree incoming
components supply input-side centering; degree-zero output uses channel norm
one. The exact-support signed mass estimates remain in their own component.

Constructive only; no attacks or predecessor/manuscript changes. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.FirstHighOne
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component profile)
open AES8.FirstHighSupportEvent (boundaryInput)
open AES8.TransferAssembly (centeredStep)
open AES8.SupportEvolution (highPart)

theorem profile_le_three (f : WordState → ℝ) :
    profile (centeredStep (highPart f)) 1 ≤
      l2 (component (boundaryInput (component f 11)) 1) +
        (l2 (component (boundaryInput (component f 12)) 1) +
          l2 (component (boundaryInput (component f 13)) 1)) := by
  rw [FirstHighNine.highPart_eq_three, TransferAssembly.centeredStep_add,
    TransferAssembly.centeredStep_add]
  have h11 := FirstHighZero.positive_component_profile_le_projected f 11 (by decide) 1
  have h12 := FirstHighZero.positive_component_profile_le_projected f 12 (by decide) 1
  have h13 := FirstHighZero.positive_component_profile_le_projected f 13 (by decide) 1
  change profile (centeredStep (component f 11)) 1 ≤
    SharpWordNorm.rho ^ 0 * l2 (component (boundaryInput (component f 11)) 1) at h11
  change profile (centeredStep (component f 12)) 1 ≤
    SharpWordNorm.rho ^ 0 * l2 (component (boundaryInput (component f 12)) 1) at h12
  change profile (centeredStep (component f 13)) 1 ≤
    SharpWordNorm.rho ^ 0 * l2 (component (boundaryInput (component f 13)) 1) at h13
  simp only [pow_zero, _root_.one_mul] at h11 h12 h13
  calc
    _ ≤ profile (centeredStep (component f 11)) 1 +
        (profile (centeredStep (component f 12)) 1 + profile (centeredStep (component f 13)) 1) :=
      (TransferAssembly.profile_add_le _ _ 1).trans
        (add_le_add le_rfl (TransferAssembly.profile_add_le _ _ 1))
    _ ≤ _ := add_le_add h11 (add_le_add h12 h13)

/-- Universal actual nonzero-source coordinate-one candidate. This is one
first-high cap, not the full AES physical-cap theorem. -/
theorem firstHigh_one (b : AES.State) (hb : b ≠ 0) :
    profile (centeredStep (highPart (error 1 b))) 1 ≤
      (d (1 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (1 : Fin 14)) := by
  have hscaled : (2 : ℝ) ^ 80 * profile (centeredStep (highPart (error 1 b))) 1 ≤
      (1 / 100000000000) + ((11 / 10000000000) + (1 / 10000000000)) := by
    calc
      _ ≤ (2 : ℝ) ^ 80 *
          (l2 (component (boundaryInput (component (error 1 b) 11)) 1) +
            (l2 (component (boundaryInput (component (error 1 b) 12)) 1) +
              l2 (component (boundaryInput (component (error 1 b) 13)) 1))) :=
        mul_le_mul_of_nonneg_left (profile_le_three (error 1 b)) (by positivity)
      _ = (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 11)) 1) +
          ((2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 12)) 1) +
            (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 13)) 1)) := by ring
      _ ≤ _ := add_le_add (ActualOneMoment.actual_eleven_projected_length_le b hb)
        (add_le_add (ActualOneMoment.actual_twelve_projected_length_le b hb)
          (ActualOneMoment.actual_thirteen_projected_length_le b hb))
  have hn : NormalizedProfile.factor 1 = (2 : ℝ) ^ 41 * (2 : ℝ) ^ 80 := by
    norm_num [NormalizedProfile.factor, omega41]
  have ht : NormalizedProfile.factor 1 * profile (centeredStep (highPart (error 1 b))) 1 ≤
      (1000 * g (1 : Fin 14)) * d (1 : Fin 14) := by
    rw [hn, _root_.mul_assoc]
    exact (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans TwoActiveScalars.scalar_one_le
  calc
    _ ≤ ((1000 * g (1 : Fin 14)) * d (1 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      simpa only [_root_.mul_comm] using ht
    _ = _ := by ring

end AES8.FirstHighOne
