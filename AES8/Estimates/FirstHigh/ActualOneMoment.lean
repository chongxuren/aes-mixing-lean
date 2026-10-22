/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Word.ScaledEnergy
import AES8.Reductions.Source.PinnedTwoZeroMass
import AES8.Reductions.Support.TwoActiveAverage

/-! Exact-support two-active masses are formed by signed inclusion-exclusion
before squaring. Incoming eleven vanishes on both lower endpoint fibers;
incoming twelve/thirteen pay their established signed three-zero caps.
Six orthogonal constant-nonzero projectors yield the actual coordinate-one
energies and lengths.
Constructive only; no attacks or predecessor/manuscript changes. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ActualOneMoment
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component)
open AES8.FirstHighSupportEvent (boundaryInput)
open AES8.TwoActiveScalars

private theorem abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  calc
    _ = |(a + -b) + -c| := by rw [sub_eq_add_neg, sub_eq_add_neg]
    _ ≤ |a + -b| + |-c| := abs_add_le _ _
    _ ≤ (|a| + |-b|) + |-c| := add_le_add (abs_add_le a (-b)) le_rfl
    _ = _ := by rw [abs_neg, abs_neg]

theorem actual_thirteen_exact_mass_le (t : Fin 6) (b : AES.State) (hb : b ≠ 0) :
    |TwoActiveAverage.mass t (boundaryInput (component (error 1 b) 13))| ≤ thirteenExactMassCap := by
  rw [TwoActiveAverage.boundary_mass_eq_full_fibers _ (SupportProfile.component_at_zero _ 13)]
  calc
    _ ≤ |∑ g : WordMixTwoZeroFiber.G (TwoActiveAverage.inactiveMask t),
          component (error 1 b) 13 g.val| +
        |∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (TwoActiveAverage.left t)),
          component (error 1 b) 13 g.val| +
        |∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (TwoActiveAverage.right t)),
          component (error 1 b) 13 g.val| := abs_sub_sub_le _ _ _
    _ ≤ thirteenFullMassCap + ActualZeroMoment.thirteenMassCap + ActualZeroMoment.thirteenMassCap :=
      add_le_add
        (add_le_add (ActualTwoActiveMass.actual_thirteen_full_mass_le _ (TwoActiveAverage.inactiveMask_size t) b hb)
          (ActualZeroMoment.actual_thirteen_mass_le _ (OneActiveAverage.inactiveMask_size _) b hb))
        (ActualZeroMoment.actual_thirteen_mass_le _ (OneActiveAverage.inactiveMask_size _) b hb)
    _ = thirteenExactMassCap := by unfold thirteenExactMassCap; ring

theorem actual_twelve_exact_mass_le (t : Fin 6) (b : AES.State) (hb : b ≠ 0) :
    |TwoActiveAverage.mass t (boundaryInput (component (error 1 b) 12))| ≤ twelveExactMassCap := by
  rw [TwoActiveAverage.boundary_mass_eq_full_fibers _ (SupportProfile.component_at_zero _ 12)]
  calc
    _ ≤ |∑ g : WordMixTwoZeroFiber.G (TwoActiveAverage.inactiveMask t),
          component (error 1 b) 12 g.val| +
        |∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (TwoActiveAverage.left t)),
          component (error 1 b) 12 g.val| +
        |∑ g : WordMixThreeZeroFiber.G (OneActiveAverage.inactiveMask (TwoActiveAverage.right t)),
          component (error 1 b) 12 g.val| := abs_sub_sub_le _ _ _
    _ ≤ 4 * twelvePatternFullMassCap + 4 * ActualZeroMoment.twelvePatternMassCap +
        4 * ActualZeroMoment.twelvePatternMassCap :=
      add_le_add
        (add_le_add (ActualTwoActiveMass.actual_twelve_full_mass_le _ (TwoActiveAverage.inactiveMask_size t) b hb)
          (ActualZeroMoment.actual_twelve_mass_le _ (OneActiveAverage.inactiveMask_size _) b hb))
        (ActualZeroMoment.actual_twelve_mass_le _ (OneActiveAverage.inactiveMask_size _) b hb)
    _ = twelveExactMassCap := by unfold twelveExactMassCap; ring

theorem actual_eleven_exact_mass_le (t : Fin 6) (b : AES.State) (hb : b ≠ 0) :
    |TwoActiveAverage.mass t (boundaryInput (component (error 1 b) 11))| ≤ elevenExactMassCap := by
  rw [TwoActiveAverage.boundary_mass_eq_full_fibers _ (SupportProfile.component_at_zero _ 11),
    PinnedTwoZeroMass.component_eleven_three_zero_mass _ _ (OneActiveAverage.inactiveMask_size _),
    PinnedTwoZeroMass.component_eleven_three_zero_mass _ _ (OneActiveAverage.inactiveMask_size _),
    sub_zero, sub_zero]
  exact PinnedTwoZeroMass.actual_eleven_full_mass_le _ (TwoActiveAverage.inactiveMask_size t) b hb

/-- The six exact-support rank-one energies share the same explicit cap. -/
theorem projected_energy_le (f : WordState → ℝ) (cap : ℝ)
    (hmass : ∀ t : Fin 6, |TwoActiveAverage.mass t (boundaryInput f)| ≤ cap) :
    (∑ y, component (boundaryInput f) 1 y ^ 2) ≤ 6 * cap ^ 2 / (q - 1) ^ 2 := by
  rw [TwoActiveAverage.component_one_energy]
  have hd : ActivityAverageEnergy.denominator AES.Word = q - 1 := by
    unfold ActivityAverageEnergy.denominator
    rw [AES.word_card]
    norm_num [q]
  simp_rw [hd]
  calc
    _ ≤ ∑ _t : Fin 6, cap ^ 2 / (q - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) (hmass t) 2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem actual_eleven_projected_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 11)) 1 y ^ 2) ≤ elevenBudget :=
  projected_energy_le _ elevenExactMassCap (fun t => actual_eleven_exact_mass_le t b hb)

theorem actual_twelve_projected_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 12)) 1 y ^ 2) ≤ twelveBudget :=
  projected_energy_le _ twelveExactMassCap (fun t => actual_twelve_exact_mass_le t b hb)

theorem actual_thirteen_projected_energy_le (b : AES.State) (hb : b ≠ 0) :
    (∑ y, component (boundaryInput (component (error 1 b) 13)) 1 y ^ 2) ≤ thirteenBudget :=
  projected_energy_le _ thirteenExactMassCap (fun t => actual_thirteen_exact_mass_le t b hb)

theorem actual_eleven_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 11)) 1) ≤ 1 / 100000000000 := by
  exact ScaledEnergy.aes_scaled_l2_le _ _ _ (by norm_num)
    (actual_eleven_projected_energy_le b hb) eleven_budget_le

theorem actual_twelve_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 12)) 1) ≤ 11 / 10000000000 := by
  exact ScaledEnergy.aes_scaled_l2_le _ _ _ (by norm_num)
    (actual_twelve_projected_energy_le b hb) twelve_budget_le

theorem actual_thirteen_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 13)) 1) ≤ 1 / 10000000000 := by
  exact ScaledEnergy.aes_scaled_l2_le _ _ _ (by norm_num)
    (actual_thirteen_projected_energy_le b hb) thirteen_budget_le

end AES8.ActualOneMoment
