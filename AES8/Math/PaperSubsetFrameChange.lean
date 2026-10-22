import AES8.Math.PaperSubsetArrayNorms

/-! Exact size-coordinate form of the paper's inverse activity-frame change.
The one-coordinate absolute change is [[1,1/sqrt255],[0,16/sqrt255]].
The matrices below are its symmetric powers in normalized size columns.
Their Gram roots are products of 16/15 and 16/17. This supplies exactly the
printed inverse-frame loss, separately from the subset-array calculation.
Build-only constructive candidate; no execution or review is claimed here. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetFrameChange
open PaperKernelBounds PaperSubsetArrayNorms
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def frame2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, Real.sqrt 2*Real.sqrt 255/255, 1/255;
     0, 16*Real.sqrt 255/255, 16*Real.sqrt 2/255;
     0, 0, 256/255]

def frame3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, Real.sqrt 3*Real.sqrt 255/255, Real.sqrt 3/255, Real.sqrt 255/65025;
     0, 16*Real.sqrt 255/255, 32/255, 16*Real.sqrt 3*Real.sqrt 255/65025;
     0, 0, 256/255, 256*Real.sqrt 3*Real.sqrt 255/65025;
     0, 0, 0, 4096*Real.sqrt 255/65025]

def gram2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, Real.sqrt 2*Real.sqrt 255/255, 1/255;
     Real.sqrt 2*Real.sqrt 255/255, 258/255, 257*Real.sqrt 2*Real.sqrt 255/65025;
     1/255, 257*Real.sqrt 2*Real.sqrt 255/65025, 66049/65025]

def gram3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, Real.sqrt 3*Real.sqrt 255/255, Real.sqrt 3/255, Real.sqrt 255/65025;
     Real.sqrt 3*Real.sqrt 255/255, 259/255, 515*Real.sqrt 255/65025,
       257*Real.sqrt 3/65025;
     Real.sqrt 3/255, 515*Real.sqrt 255/65025, 66563/65025,
       66049*Real.sqrt 3*Real.sqrt 255/16581375;
     Real.sqrt 255/65025, 257*Real.sqrt 3/65025,
       66049*Real.sqrt 3*Real.sqrt 255/16581375, 16974593/16581375]

theorem frame2_gram : frame2.transpose * frame2 = gram2 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h255 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 255)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frame2, gram2, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [h2, h255] <;> ring

theorem frame3_gram : frame3.transpose * frame3 = gram3 := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h255 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 255)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frame3, gram3, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [h3, h255] <;> ring

theorem gram2_symmetric : gram2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram2, Matrix.conjTranspose_apply]

theorem gram3_symmetric : gram3.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram3, Matrix.conjTranspose_apply]

theorem gram2_charpoly (x : ℝ) : gram2.charpoly.eval x =
    (x-256/225)*(x-256/255)*(x-256/289) := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h255 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 255)
  rw [Matrix.eval_charpoly]
  simp [gram2, Matrix.det_fin_three, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply]
  ring_nf
  simp only [h2, h255]
  ring

theorem gram3_charpoly (x : ℝ) : gram3.charpoly.eval x =
    (x-4096/3375)*(x-4096/3825)*(x-4096/4335)*(x-4096/4913) := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h34 : Real.sqrt 3 ^ 4 = (9:ℝ) := by nlinarith [sq_nonneg (Real.sqrt 3 ^ 2-3)]
  have h255 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 255)
  have h2554 : Real.sqrt 255 ^ 4 = (65025:ℝ) := by
    calc _ = (Real.sqrt 255 ^ 2)^2 := by ring
         _ = _ := by rw [h255]; norm_num
  rw [Matrix.eval_charpoly]
  simp [gram3, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  simp only [h3, h34, h255, h2554]
  ring

theorem gram2_norm : ‖kernelOperator gram2‖ = (16/15:ℝ)^2 := by
  apply norm_eq_of_charpoly_roots gram2 gram2_symmetric _ (by norm_num)
  · intro x hx
    rw [gram2_charpoly] at hx
    have hh : x=256/225 ∨ x=256/255 ∨ x=256/289 := by
      simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using hx
    rcases hh with rfl|rfl|rfl <;> norm_num
  · rw [gram2_charpoly]; norm_num

theorem gram3_norm : ‖kernelOperator gram3‖ = (16/15:ℝ)^3 := by
  apply norm_eq_of_charpoly_roots gram3 gram3_symmetric _ (by norm_num)
  · intro x hx
    rw [gram3_charpoly] at hx
    have hh : x=4096/3375 ∨ x=4096/3825 ∨ x=4096/4335 ∨ x=4096/4913 := by
      simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using hx
    rcases hh with rfl|rfl|rfl|rfl <;> norm_num
  · rw [gram3_charpoly]; norm_num

theorem frame2_norm : ‖kernelOperator frame2‖ = (16/15:ℝ) := by
  have h := norm_sq_eq_gram frame2
  rw [frame2_gram, gram2_norm] at h
  nlinarith [norm_nonneg (kernelOperator frame2)]

theorem frame3_norm : ‖kernelOperator frame3‖ = Real.sqrt ((16/15:ℝ)^3) := by
  have h := norm_sq_eq_gram frame3
  rw [frame3_gram, gram3_norm] at h
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (16/15:ℝ)^3)
  nlinarith [norm_nonneg (kernelOperator frame3), Real.sqrt_nonneg ((16/15:ℝ)^3)]

end AES8.PaperSubsetFrameChange
