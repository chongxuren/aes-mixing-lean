import AES8.Estimates.Word.PaperSubsetSupportNorms
import AES8.Estimates.Word.PaperSubsetSupportFactor11
import AES8.Estimates.Word.PaperSubsetSupportFactor12
import AES8.Estimates.Word.PaperSubsetSupportFactor22

/-! Actual support norm bounds from exact finite sandwiches and printed arrays. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetSupportBridge
open AESMixing PaperKernelBounds PaperSubsetSizeCompression PaperSubsetArrayNorms
open PaperSubsetFrameChange PaperActivityArrayBlocks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

theorem support11_printed : ‖kernelOperator (supportIncidenceComparison 1 1)‖≤printed11 := by
  rw [support_norm, support11_factor]
  change ‖kernelOperator (fun (a : Fin 4) (b : Fin 4) =>
    (4:ℝ) * (frame3.transpose * middle11 * frame3) a b)‖ ≤ printed11
  rw [scaled_norm]
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤4)]
  exact (mul_le_mul_of_nonneg_left (sandwich_norm frame3 middle11 frame3
    _ _ _ (by positivity) (by norm_num) (by positivity)
    frame3_norm.le middle11_norm.le frame3_norm.le) (by norm_num)).trans_eq (by unfold printed11; ring)

theorem support12_printed : ‖kernelOperator (supportIncidenceComparison 1 2)‖≤printed12 := by
  rw [support_norm, support12_factor]
  change ‖kernelOperator (fun (a : Fin 4) (b : Fin 3) =>
    (2*Real.sqrt 6) * (frame3.transpose * middle12 * frame2) a b)‖ ≤ printed12
  rw [scaled_norm, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (sandwich_norm frame3 middle12 frame2
    _ _ _ (by positivity) (by positivity) (by norm_num)
    frame3_norm.le middle12_norm.le frame2_norm.le) (by positivity)).trans_eq (by unfold printed12; ring)

theorem support22_printed : ‖kernelOperator (supportIncidenceComparison 2 2)‖≤printed22 := by
  rw [support_norm, support22_factor]
  change ‖kernelOperator (fun (a : Fin 3) (b : Fin 3) =>
    (6:ℝ) * (frame2.transpose * middle22 * frame2) a b)‖ ≤ printed22
  rw [scaled_norm]
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤6)]
  exact (mul_le_mul_of_nonneg_left (sandwich_norm frame2 middle22 frame2
    _ _ _ (by norm_num) (by positivity) (by norm_num)
    frame2_norm.le middle22_norm.le frame2_norm.le) (by norm_num)).trans_eq (by unfold printed22; ring)

end AES8.PaperSubsetSupportBridge
