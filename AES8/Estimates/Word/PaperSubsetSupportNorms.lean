import AES8.Estimates.Word.PaperSubsetSupportCore

/-! Independent operator-norm helpers and exact printed subset-array norms. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetSupportBridge
open AESMixing PaperKernelBounds PaperSubsetSizeCompression PaperSubsetArrayNorms
open PaperSubsetFrameChange PaperActivityArrayBlocks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

theorem matrix_mul_norm_le {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) :
    ‖kernelOperator (A*B)‖ ≤ ‖kernelOperator A‖*‖kernelOperator B‖ := by
  change ‖kernelOperator (kernelCompose A B)‖ ≤ _
  rw [PaperKernelComposition.operator_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem transpose_norm_le {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I J ℝ) (c : ℝ) (hc : 0≤c)
    (h : ‖kernelOperator A‖≤c) : ‖kernelOperator A.transpose‖≤c := by
  exact norm_le_of_energyBound _ c hc
    (energyBound_transpose A c (energyBound_of_norm A c hc h))

theorem scaled_norm {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (c : ℝ) (A : Matrix J I ℝ) :
    ‖kernelOperator (fun a b => c*A a b)‖ = |c| * ‖kernelOperator A‖ := by
  rw [PaperKernelLinear.operator_smul, norm_smul, Real.norm_eq_abs]

theorem middle11_norm : ‖kernelOperator middle11‖ = 3/4096 := by
  have hs := subset_degree11_norm
  rw [subset_norm, compressed11] at hs
  have he : middle11 = fun a b => (1/4096:ℝ)*matrix11 a b := by ext; simp [middle11, div_eq_mul_inv, mul_comm]
  rw [he, scaled_norm, hs]; norm_num

theorem middle12_norm : ‖kernelOperator middle12‖ = Real.sqrt (8+2*Real.sqrt 13)/256 := by
  have hs := subset_degree12_norm
  rw [subset_norm, compressed12] at hs
  have he : middle12 = fun a b => (1/256:ℝ)*matrix12 a b := by ext; simp [middle12, div_eq_mul_inv, mul_comm]
  rw [he, scaled_norm, hs]; norm_num; ring

theorem middle22_norm : ‖kernelOperator middle22‖ =
    (3/256+Real.sqrt ((1/256:ℝ)^2+16*(1/16:ℝ)^2))/2 := by
  have hs := subset_degree22_norm (1/16) (1/256) (by norm_num) (by norm_num)
  rw [subset_norm, compressed22] at hs
  calc
    _ = (3*(1/256)+Real.sqrt ((1/256:ℝ)^2+16*(1/16:ℝ)^2))/2 := hs
    _ = _ := by ring

def printed11 : ℝ := 4*Real.sqrt ((16/15:ℝ)^3)*(3/4096)*Real.sqrt ((16/15:ℝ)^3)
def printed12 : ℝ := (2*Real.sqrt 6)*Real.sqrt ((16/15:ℝ)^3)*
  (Real.sqrt (8+2*Real.sqrt 13)/256)*(16/15)
def printed22 : ℝ := 6*(16/15)*
  ((3/256+Real.sqrt ((1/256:ℝ)^2+16*(1/16:ℝ)^2))/2)*(16/15)

theorem sandwich_norm {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (L : Matrix I I ℝ) (M : Matrix I J ℝ)
    (R : Matrix J J ℝ) (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hL : ‖kernelOperator L‖≤a) (hM : ‖kernelOperator M‖≤b)
    (hR : ‖kernelOperator R‖≤c) : ‖kernelOperator (L.transpose*M*R)‖≤a*b*c := by
  calc
    _ ≤ ‖kernelOperator (L.transpose*M)‖*‖kernelOperator R‖ := matrix_mul_norm_le _ _
    _ ≤ (‖kernelOperator L.transpose‖*‖kernelOperator M‖)*‖kernelOperator R‖ :=
      mul_le_mul_of_nonneg_right (matrix_mul_norm_le _ _) (norm_nonneg _)
    _ ≤ (a*b)*c := mul_le_mul (mul_le_mul (transpose_norm_le L a ha hL) hM
      (norm_nonneg _) ha) hR (norm_nonneg _) (mul_nonneg ha hb)


end AES8.PaperSubsetSupportBridge
