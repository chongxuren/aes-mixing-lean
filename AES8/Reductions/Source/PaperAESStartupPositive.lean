import AES8.Reductions.Source.PaperAESStartupComponent
import AES8.Reductions.Source.PaperAESStartupCommon
import AES8.Recurrence.PaperComparisonReal
import AES8.Recurrence.NormalizedProfile

/-!
# The current startup allowance on every positive residual component

The actual-source energy bridge is combined with independently checked exact
rational margins. The ordinary source bound remains an explicit input.
The activity components and total startup assembly are separate leaves.
Constructive proofs only; no attacks or assumed startup/profile cap.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupPositive
open AESMixing
open PaperAESStartupSource PaperAESStartupComponent
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Every positive-degree actual energy fits the common 900 allowance.
Zero events, one-source Gram bounds, and several-source response bounds are
selected using the actual input support; none is an assumed component bound. -/
theorem scaled_positive_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c) :
    (4294967296 : ℝ)^5 *
      (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y ^ 2) ≤
      ((PaperStartupScalars.allowance c : ℚ) : ℝ)^2 := by
  let w : Fin 5 := ⟨(active a).card, by
    have h := Finset.card_le_univ (active a)
    norm_num at h
    omega⟩
  have hwpos : 0 < w.val := (active_nonempty a ha).card_pos
  have htype := PaperSupportProfileJoin.typeOf_eq c
  have htle : SupportProfile.supportSize c ≤ 4 := by
    have h := PaperSupportProfileJoin.supportSize_lt c
    omega
  by_cases hw : w.val ≤ 4-SupportProfile.supportSize c
  · rw [actual_residual_energy_zero a ha c hi hw, mul_zero]
    exact sq_nonneg _
  have hres := actual_residual_energy_le raw a c hi (by dsimp [w] at hw; omega)
  by_cases ht : SupportProfile.supportSize c < 4
  · have h := PaperStartupScalars.proper_residual_allowance c w
      (by simpa only [htype] using hi) (by simpa only [htype] using ht)
      (by simpa only [htype] using (Nat.lt_of_not_ge hw))
    have hr : (PaperStartupScalars.residualSquared (SupportProfile.residualDegree c)
        (SupportProfile.supportSize c) w.val : ℚ) ≤
        ((PaperStartupScalars.allowance c : ℚ) : ℝ)^2 := by
      rw [htype] at h
      exact_mod_cast h
    exact hres.trans hr
  have ht4 : SupportProfile.supportSize c = 4 := by omega
  by_cases hi1 : SupportProfile.residualDegree c = 1
  · have hc : c = 7 := (by decide : ∀ c : Fin 14,
        SupportProfile.residualDegree c = 1 → SupportProfile.supportSize c = 4 → c = 7)
      c hi1 ht4
    subst c
    have h := PaperStartupScalars.full_degree_one_allowance w hwpos
    have hr : (PaperStartupScalars.residualSquared 1 4 w.val : ℚ) ≤
        ((PaperStartupScalars.allowance 7 : ℚ) : ℝ)^2 := by exact_mod_cast h
    exact hres.trans hr
  have hi2 : 2 ≤ SupportProfile.residualDegree c := by omega
  have hcommon : (4294967296 : ℝ)^5 *
      (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y ^ 2) ≤
      (PaperStartupScalars.commonSquared (SupportProfile.residualDegree c) : ℚ) := by
    by_cases hw1 : w.val = 1
    · exact PaperAESStartupCommon.actual_common_energy_le raw a hw1 c hi2 ht4
    · have h := PaperStartupScalars.several_full_le_common
        (PaperSupportProfileJoin.degreeIndex c) w hi2 (by omega)
      have hr : ((PaperStartupScalars.residualSquared (SupportProfile.residualDegree c) 4
          w.val : ℚ) : ℝ) ≤
          ((PaperStartupScalars.commonSquared (SupportProfile.residualDegree c) : ℚ) : ℝ) :=
        by exact_mod_cast h
      rw [ht4] at hres
      exact hres.trans hr
  have h := PaperStartupScalars.common_allowance c
    (by simpa only [htype] using hi2) (by simpa only [htype] using ht4)
  have hr : (PaperStartupScalars.commonSquared (SupportProfile.residualDegree c) : ℚ) ≤
      ((PaperStartupScalars.allowance c : ℚ) : ℝ)^2 := by
    rw [htype] at h
    exact_mod_cast h
  exact hcommon.trans hr

/-- Counting-measure norm form of the positive-residual startup allowance. -/
theorem scaled_positive_profile_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c) :
    (2 : ℝ)^80 * SupportProfile.actual a 0 c ≤
      (PaperStartupScalars.allowance c : ℚ) := by
  have h := scaled_positive_energy_le raw a ha c hi
  have hp : 0 ≤ (PaperStartupScalars.allowance c : ℝ) := by
    exact_mod_cast (PaperStartupScalars.allowance_pos c).le
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (SupportProfile.actual_nonneg a 0 c)) hp).mp
  change ((2 : ℝ)^80 * l2 (SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c))^2 ≤ _
  rw [mul_pow, l2_sq]
  rw [show ((2 : ℝ)^80)^2 = (4294967296 : ℝ)^5 by norm_num]
  exact h

/-- Literal normalized-profile interface, retaining the paper's margin900. -/
theorem positive_initial_900 (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (900 * (PaperComparison.startup0 c : ℝ)) := by
  have h := scaled_positive_profile_le raw a ha c hi
  have hd : (PaperComparison.scales c : ℝ) = d c :=
    congrFun PaperComparison.real_scales_eq c
  simpa only [NormalizedProfile.factor, pow_zero, div_one,
    PaperStartupScalars.allowance, Rat.cast_mul, Rat.cast_ofNat, hd, mul_assoc,
    mul_left_comm 900 (d c)] using h

/-- The requested1000 allowance follows from the stronger900 margin. -/
theorem positive_initial (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (1000 * (PaperComparison.startup0 c : ℝ)) := by
  apply (positive_initial_900 raw a ha c hi).trans
  apply mul_le_mul_of_nonneg_left _ (NormalizedProfile.diagonal_pos c).le
  apply mul_le_mul_of_nonneg_right (by norm_num : (900 : ℝ) ≤ 1000)
  fin_cases c <;> norm_num [PaperComparison.startup0]

end AES8.PaperAESStartupPositive
