import AES8.Estimates.Word.PaperSubsetSupportCore

/-! Exact printed subset-array sandwich, degree 22. Build-only candidate. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetSupportBridge
open AESMixing PaperKernelBounds PaperSubsetSizeCompression PaperSubsetArrayNorms
open PaperSubsetFrameChange PaperActivityArrayBlocks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

theorem support22_factor : supportCompressed 2 2 =
    fun a b => 6 * (frame2.transpose * middle22 * frame2) a b := by
  change (fun (a : Fin 3) (b : Fin 3) => supportCompressed 2 2 a b) =
    (fun (a : Fin 3) (b : Fin 3) => 6 * (frame2.transpose * middle22 * frame2) a b)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h6 := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have h255 := Real.sq_sqrt (by norm_num : (0:ℝ)≤255)
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤4), Real.sqrt_nonneg (4:ℝ)]
  have h2553 : Real.sqrt (255:ℝ)^3 = 255*Real.sqrt 255 := by
    calc _ = Real.sqrt (255:ℝ)^2*Real.sqrt 255 := by ring
         _ = _ := by rw [h255]
  have h2554 : Real.sqrt (255:ℝ)^4 = 65025 := by
    calc _ = (Real.sqrt (255:ℝ)^2)^2 := by ring
         _ = _ := by rw [h255]; norm_num
  have h2555 : Real.sqrt (255:ℝ)^5 = 65025*Real.sqrt 255 := by
    calc _ = Real.sqrt (255:ℝ)^4*Real.sqrt 255 := by ring
         _ = _ := by rw [h2554]
  have h2556 : Real.sqrt (255:ℝ)^6 = 16581375 := by
    calc _ = (Real.sqrt (255:ℝ)^2)^3 := by ring
         _ = _ := by rw [h255]; norm_num
  have h2cube : Real.sqrt (2:ℝ)^3 = 2*Real.sqrt 2 := by
    calc _ = Real.sqrt (2:ℝ)^2*Real.sqrt 2 := by ring
         _ = _ := by rw [h2]
  unfold supportCompressed
  simp_rw [diagonal_sqrt]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [supportScale, incidenceSupportRaw,
      frame2, middle22, matrix22, Matrix.mul_apply, Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    ring_nf <;> (try simp only [h2, h2cube, h4, h6, h255, h2553, h2554, h2555, h2556]) <;> ring



end AES8.PaperSubsetSupportBridge
