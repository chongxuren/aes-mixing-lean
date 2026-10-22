import AES8.Estimates.Source.PaperAESActivityStartup
import AES8.Recurrence.PaperComparisonReal
import AES8.Recurrence.NormalizedProfile

/-! Activity-only startup allowances, obtained from the original source
event masses. Positive-residual startup and complete assembly are separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupActivity
open AESMixing PaperAESActivityStartup
set_option autoImplicit false
set_option maxRecDepth 100000

theorem scaled_activity_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : SupportProfile.residualDegree c = 0) :
    (4294967296 : ℝ)^5 *
      (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y^2) ≤
      (PaperStartupScalars.allowance c : ℝ)^2 := by
  have ht0 : 0 < SupportProfile.supportSize c :=
    (by decide : ∀ c : Fin 14, 0 < SupportProfile.supportSize c) c
  have ht4 : SupportProfile.supportSize c ≤ 4 := by
    have h := PaperSupportProfileJoin.supportSize_lt c
    omega
  have htype := PaperSupportProfileJoin.typeOf_eq c
  by_cases ht : SupportProfile.supportSize c < 4
  · have h := proper_activity_energy raw a ha (PaperSupportProfileJoin.supportIndex c) ht0 ht
    have hsc := PaperStartupScalars.proper_activity_allowance c
      (by simpa only [htype] using hi) (by simpa only [htype] using ht)
    have hsc' : (PaperStartupScalars.properActivitySquared (SupportProfile.supportSize c) : ℝ) ≤
        (PaperStartupScalars.allowance c : ℝ)^2 := by
      rw [htype] at hsc
      exact_mod_cast hsc
    rw [PaperSupportProfileJoin.component_eq, hi]
    exact h.trans hsc'
  · have he : c = 3 := (by decide : ∀ c : Fin 14,
        SupportProfile.residualDegree c = 0 → SupportProfile.supportSize c = 4 → c = 3)
      c hi (by omega)
    subst c
    have hsc : (PaperStartupScalars.fullActivitySquared : ℝ) ≤
        (PaperStartupScalars.allowance 3 : ℝ)^2 := by
      exact_mod_cast PaperStartupScalars.full_activity_allowance
    rw [PaperSupportProfileJoin.component_eq]
    exact (full_activity_energy raw a ha).trans hsc

theorem activity_initial_900 (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : SupportProfile.residualDegree c = 0) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (900 * (PaperComparison.startup0 c : ℝ)) := by
  have he := scaled_activity_energy_le raw a ha c hi
  have hp : 0 ≤ (PaperStartupScalars.allowance c : ℝ) := by
    exact_mod_cast (PaperStartupScalars.allowance_pos c).le
  have h : (2 : ℝ)^80 * SupportProfile.actual a 0 c ≤
      (PaperStartupScalars.allowance c : ℝ) := by
    apply (sq_le_sq₀ (mul_nonneg (by positivity) (SupportProfile.actual_nonneg a 0 c)) hp).mp
    change ((2 : ℝ)^80 * l2 (SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c))^2 ≤ _
    rw [mul_pow, l2_sq]
    rw [show ((2 : ℝ)^80)^2 = (4294967296 : ℝ)^5 by norm_num]
    exact he
  have hd : (PaperComparison.scales c : ℝ) = d c :=
    congrFun PaperComparison.real_scales_eq c
  simpa only [NormalizedProfile.factor, pow_zero, div_one,
    PaperStartupScalars.allowance, Rat.cast_mul, Rat.cast_ofNat, hd, mul_assoc,
    mul_left_comm 900 (d c)] using h

end AES8.PaperAESStartupActivity
