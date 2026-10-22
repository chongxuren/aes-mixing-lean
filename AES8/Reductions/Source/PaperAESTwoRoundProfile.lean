import AES8.Reductions.Source.PaperAESTwoRoundSource
import AES8.Reductions.Source.PaperProductSourceSupport
import AES8.Reductions.Support.PaperSupportProfileJoin
import AES8.Recurrence.PaperFirstReturnComparison
import AES8.Recurrence.PaperComparisonReal

/-! Actual two-round source profile and its several-source envelope.
The support mask is retained before applying the common return matrix.
The rational comparison checks this specific source vector, not an operator norm. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESTwoRoundProfile
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift
open PaperAESTwoRoundSource PaperSupportProfileJoin PaperComparison
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem component_eq (a : AES.State) (c : Fin 14) :
    SupportProfile.component (AESPaper.GroupedLaw.groupedLaw 0 a) c =
      if supportCount (sourceMask a) = SupportProfile.supportSize c then
        fixedComponent (0 : AES.Word) (AESPaper.GroupedLaw.groupedLaw 0 a)
          (SupportProfile.residualDegree c) (sourceMask a) else 0 := by
  rw [PaperSupportProfileJoin.component_eq, grouped_source]
  exact PaperProductSourceSupport.component_eq_fixed 0 AES.wordSuperboxKernel
    AES.word_superbox_pointed (AESPaper.StartingWord.sourceInput a) (sourceMask a)
    (by intro k; simp [sourceMask]) _ _

theorem profile_le (a : AES.State) (c : Fin 14) :
    SupportProfile.profile (AESPaper.GroupedLaw.groupedLaw 0 a) c ≤
      if supportCount (sourceMask a) = SupportProfile.supportSize c then
        Real.sqrt (energyBound (SupportProfile.residualDegree c)
          (SupportProfile.supportSize c)) else 0 := by
  unfold SupportProfile.profile
  rw [component_eq]
  split_ifs with h
  · simpa only [PaperSupportProfileJoin.degreeIndex, h] using fixed_norm_le a (degreeIndex c)
  · simp [l2]

/-- Exact squared rational checks for the current several-source vector. -/
theorem several_length_le (c : Fin 14) (hc : 2 ≤ SupportProfile.supportSize c) :
    Real.sqrt (energyBound (SupportProfile.residualDegree c) (SupportProfile.supportSize c)) ≤
      (1000 * (scales c : ℝ) / (omega41 * (2 : ℝ)^80)) *
        (PaperFirstReturnComparison.severalSource c : ℝ) := by
  fin_cases c <;> norm_num [SupportProfile.supportSize] at hc
  all_goals
    apply Real.sqrt_le_iff.mpr
    constructor <;>
    norm_num [SupportProfile.residualDegree, SupportProfile.supportSize,
      energyBound, Nat.choose, omega41, scales, PaperFirstReturnComparison.severalSource]

theorem severalSource_nonneg (c : Fin 14) :
    0 ≤ (PaperFirstReturnComparison.severalSource c : ℝ) := by
  fin_cases c <;> norm_num [PaperFirstReturnComparison.severalSource]

/-- Literal eq. aesasm-source-a for the actual initial distribution. -/
theorem several_scaled_profile_le (a : AES.State)
    (ha : 2 ≤ supportCount (sourceMask a)) (c : Fin 14) :
    (omega41 * (2 : ℝ)^80 / (1000 * d c)) *
      SupportProfile.profile (AESPaper.GroupedLaw.groupedLaw 0 a) c ≤
        (PaperFirstReturnComparison.severalSource c : ℝ) := by
  have hd := NormalizedProfile.diagonal_pos c
  have hf : 0 ≤ omega41 * (2 : ℝ)^80 / (1000 * d c) := by
    exact div_nonneg (mul_nonneg omega41_pos.le (by positivity)) (by positivity)
  have hb := mul_le_mul_of_nonneg_left (profile_le a c) hf
  by_cases hs : supportCount (sourceMask a) = SupportProfile.supportSize c
  · rw [if_pos hs] at hb
    have hlen := several_length_le c (hs ▸ ha)
    have hscale : (scales c : ℝ) = d c := congrFun real_scales_eq c
    rw [hscale] at hlen
    apply hb.trans
    calc
      _ ≤ (omega41 * (2 : ℝ)^80 / (1000 * d c)) *
          ((1000 * d c / (omega41 * (2 : ℝ)^80)) *
            (PaperFirstReturnComparison.severalSource c : ℝ)) :=
        mul_le_mul_of_nonneg_left hlen hf
      _ = _ := by field_simp [hd.ne', omega41_pos.ne'] <;> ring
  · rw [if_neg hs, mul_zero] at hb
    exact hb.trans (severalSource_nonneg c)

end AES8.PaperAESTwoRoundProfile
