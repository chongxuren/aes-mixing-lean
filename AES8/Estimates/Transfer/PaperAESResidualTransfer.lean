import AES8.Estimates.Transfer.PaperAESSupportStepRational
import AES8.Reductions.Support.PaperSupportCentering
import AES8.Recurrence.PaperComparisonReal

/-! The actual centered one-step estimate for every positive low-degree input
column of the current paper matrix. Degree-zero input caps remain separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESResidualTransfer
open AESMixing AESMixing.AES PaperComparison
open PaperSupportProfileJoin TransferAssembly
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem physicalCoeff_eq (a b : Fin 14)
    (hb : SupportProfile.residualDegree b ≠ 0)
    (hblow : SupportProfile.residualDegree b ≤ 2) :
    physicalCoeff 1 a b (realStep a b) =
      ((support (SupportProfile.residualDegree a) (SupportProfile.supportSize a)
        (SupportProfile.residualDegree b) (SupportProfile.supportSize b) stepGraph : ℝ) /
        4294967296) := by
  have ha0 : d a ≠ 0 := (NormalizedProfile.diagonal_pos a).ne'
  have hb0 : d b ≠ 0 := (NormalizedProfile.diagonal_pos b).ne'
  have haScale : (scales a : ℝ) = d a := congrFun real_scales_eq a
  have hbScale : (scales b : ℝ) = d b := congrFun real_scales_eq b
  unfold physicalCoeff realStep stepMatrix
  rw [typeOf_eq a, typeOf_eq b]
  dsimp only
  rw [if_pos hblow]
  simp only [stepComponent, hb, and_false, if_false]
  push_cast
  rw [haScale, hbScale]
  unfold omega41
  field_simp [ha0, hb0]
  <;> ring

/-- All 98 actual matrix entries whose input degree is one or two. -/
theorem low_residual_cap (f : WordState → ℝ) (a b : Fin 14)
    (hb : SupportProfile.residualDegree b ≠ 0)
    (hblow : SupportProfile.residualDegree b ≤ 2) :
    SupportProfile.profile (centeredStep (SupportProfile.component f b)) a ≤
      physicalCoeff 1 a b (realStep a b) * SupportProfile.profile f b := by
  have hn : 0 < SupportProfile.residualDegree a + SupportProfile.residualDegree b := by omega
  rw [physicalCoeff_eq a b hb hblow]
  have he := PaperSupportCentering.centered_block_eq f a b hn
  have h := PaperAESSupportStepRational.profile_norm_le a b hn false f
  unfold SupportProfile.profile at h ⊢
  rw [he]
  exact h

end AES8.PaperAESResidualTransfer
