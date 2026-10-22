import AES8.Estimates.Source.PaperAESStartupActivity
import AES8.Reductions.Source.PaperAESStartupPositive

/-! The current four-round initializer, assembled from all fourteen actual
components. Only the ordinary word point bound remains explicit. -/
noncomputable section
namespace AES8.PaperAESCurrentStartup
open AESMixing
set_option autoImplicit false

theorem initial_900 (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (900 * (PaperComparison.startup0 c : ℝ)) := by
  by_cases hi : SupportProfile.residualDegree c = 0
  · exact PaperAESStartupActivity.activity_initial_900 raw a ha c hi
  · exact PaperAESStartupPositive.positive_initial_900 raw a ha c (by omega)

theorem initial (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (c : Fin 14) :
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 c ≤
      d c * (1000 * (PaperComparison.startup0 c : ℝ)) := by
  apply (initial_900 raw a ha c).trans
  apply mul_le_mul_of_nonneg_left _ (NormalizedProfile.diagonal_pos c).le
  apply mul_le_mul_of_nonneg_right (by norm_num : (900 : ℝ) ≤ 1000)
  fin_cases c <;> norm_num [PaperComparison.startup0]

end AES8.PaperAESCurrentStartup
