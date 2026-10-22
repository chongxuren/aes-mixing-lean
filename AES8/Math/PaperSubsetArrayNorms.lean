import AES8.Math.PaperSubsetSizeCompression
import AES8.Math.PaperFiniteSymmetricNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Exact small spectral certificates for the three subset arrays.
The generic lossless compression is separate from these matrix calculations.
Paper binding: 1906c42e047dabe7dcb66393cdb9658a2a7bd800,
12-word-resources.tex:454--497. No numerical norm premise is used. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSubsetArrayNorms
open PaperKernelBounds PaperSubsetSizeCompression PaperFiniteSymmetricNorm
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3600000

/-- Reuse the eigenbasis-to-operator bridge on a complete real root certificate. -/
theorem norm_eq_of_charpoly_roots {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x : ℝ, A.charpoly.eval x = 0 → |x| ≤ r)
    (hroot : A.charpoly.eval r = 0) : ‖kernelOperator A‖ = r := by
  apply le_antisymm
  · apply norm_le_eigenvalue_bound A hA r hr
    intro i
    exact hbound _ (Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      (hA.eigenvalues_mem_spectrum_real i))
  · have hs := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    rw [hA.spectrum_real_eq_range_eigenvalues] at hs
    obtain ⟨i, hi⟩ := hs
    rw [← abs_of_nonneg hr, ← hi]
    exact abs_eigenvalue_le_norm A hA i

/-- The ordinary rectangular operator norm squared is the Gram norm. -/
theorem norm_sq_eq_gram {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix J I ℝ) :
    ‖kernelOperator A‖^2 = ‖kernelOperator (A.transpose*A)‖ := by
  have ha : kernelOperator A.transpose = (kernelOperator A).adjoint := by
    have ht : A.transpose = A.conjTranspose := by ext; simp
    unfold kernelOperator
    rw [ht, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_toContinuousLinearMap]
  have hc : kernelOperator (A.transpose*A) =
      (kernelOperator A.transpose).comp (kernelOperator A) := by
    ext f i
    simp only [kernelOperator_apply, kernelAction, Matrix.mul_apply,
      Matrix.transpose_apply, ContinuousLinearMap.comp_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hc, ha, ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

def degree11 (t : ℕ) : ℝ := if t = 3 then 1 else 0
def degree12 (t : ℕ) : ℝ := if t = 2 ∨ t = 3 then 1 else 0
def degree22 (A B : ℝ) (t : ℕ) : ℝ :=
  if t = 1 ∨ t = 3 then A else if t = 2 then B else 0

def matrix11 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,1; 0,0,3,0; 0,3,0,0; 1,0,0,0]

def matrix12 : Matrix (Fin 4) (Fin 3) ℝ :=
  !![0,0,1; 0,Real.sqrt 3*Real.sqrt 2,Real.sqrt 3;
    Real.sqrt 3,Real.sqrt 3*Real.sqrt 2,0; 1,0,0]

def gram12 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![4,3*Real.sqrt 2,0; 3*Real.sqrt 2,12,3*Real.sqrt 2;
    0,3*Real.sqrt 2,4]

def matrix22 (A B : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,Real.sqrt 2*A,B; Real.sqrt 2*A,2*B,Real.sqrt 2*A;
    B,Real.sqrt 2*A,0]

theorem compressed11 : compressed 3 3 degree11 = matrix11 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compressed, sizeScale, degree11, matrix11, Nat.choose] <;> nlinarith

theorem compressed12 : compressed 3 2 degree12 = matrix12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compressed, sizeScale, degree12, matrix12, Nat.choose] <;> ring

theorem compressed22 (A B : ℝ) : compressed 2 2 (degree22 A B) = matrix22 A B := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compressed, sizeScale, degree22, matrix22, Nat.choose] <;>
    ring_nf <;> simp only [hs] <;> ring

theorem matrix11_symmetric : matrix11.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix11, Matrix.conjTranspose_apply]

theorem matrix11_charpoly (x : ℝ) :
    matrix11.charpoly.eval x = (x-1)*(x+1)*(x-3)*(x+3) := by
  rw [Matrix.eval_charpoly]
  simp [matrix11, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem matrix11_norm : ‖kernelOperator matrix11‖ = 3 := by
  apply norm_eq_of_charpoly_roots matrix11 matrix11_symmetric 3 (by norm_num)
  · intro x hx
    rw [matrix11_charpoly] at hx
    have hh : x=1 ∨ x = -1 ∨ x=3 ∨ x = -3 := by
      simpa only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hx
    rcases hh with rfl|rfl|rfl|rfl <;> norm_num
  · rw [matrix11_charpoly]
    norm_num

theorem matrix12_gram : matrix12.transpose*matrix12 = gram12 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix12, gram12, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [h2, h3] <;> ring

theorem gram12_symmetric : gram12.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram12, Matrix.conjTranspose_apply]

theorem gram12_charpoly (x : ℝ) :
    gram12.charpoly.eval x = (x-4)*((x-8)^2-52) := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [Matrix.eval_charpoly]
  simp [gram12, Matrix.det_fin_three, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply]
  ring_nf
  simp only [h2]
  ring

theorem gram12_roots (x : ℝ) : gram12.charpoly.eval x = 0 ↔
    x=4 ∨ x=8-2*Real.sqrt 13 ∨ x=8+2*Real.sqrt 13 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 13)
  have hq : (x-8)^2-52 = (x-(8-2*Real.sqrt 13))*(x-(8+2*Real.sqrt 13)) := by
    nlinarith only [hs]
  rw [gram12_charpoly, hq, mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero]

theorem gram12_norm : ‖kernelOperator gram12‖ = 8+2*Real.sqrt 13 := by
  have hs := Real.sqrt_nonneg (13:ℝ)
  apply norm_eq_of_charpoly_roots gram12 gram12_symmetric _ (by positivity)
  · intro x hx
    rcases (gram12_roots x).mp hx with h|h|h
    · rw [h]
      norm_num <;> linarith
    · rw [h]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [h, abs_of_nonneg (by positivity)]
  · exact (gram12_roots _).mpr (Or.inr (Or.inr rfl))

/-- All three Gram eigenvalues, as the exact characteristic-root statement. -/
theorem degree12_gram_roots (x : ℝ) :
    (matrix12.transpose*matrix12).charpoly.eval x = 0 ↔
      x=4 ∨ x=8-2*Real.sqrt 13 ∨ x=8+2*Real.sqrt 13 := by
  rw [matrix12_gram]
  exact gram12_roots x

theorem matrix12_norm : ‖kernelOperator matrix12‖ = Real.sqrt (8+2*Real.sqrt 13) := by
  have h := norm_sq_eq_gram matrix12
  rw [matrix12_gram, gram12_norm] at h
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8+2*Real.sqrt 13)
  nlinarith [norm_nonneg (kernelOperator matrix12), Real.sqrt_nonneg (8+2*Real.sqrt 13)]

def radius22 (A B : ℝ) : ℝ := (3*B+Real.sqrt (B^2+16*A^2))/2
def lower22 (A B : ℝ) : ℝ := (3*B-Real.sqrt (B^2+16*A^2))/2

theorem matrix22_symmetric (A B : ℝ) : (matrix22 A B).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix22, Matrix.conjTranspose_apply]

theorem matrix22_charpoly (A B x : ℝ) :
    (matrix22 A B).charpoly.eval x = (x+B)*(x^2-3*B*x+2*B^2-4*A^2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [Matrix.eval_charpoly]
  simp [matrix22, Matrix.det_fin_three, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply]
  ring_nf
  simp only [hs]
  ring

theorem matrix22_roots (A B x : ℝ) :
    (matrix22 A B).charpoly.eval x = 0 ↔
      x = -B ∨ x = lower22 A B ∨ x = radius22 A B := by
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ B^2+16*A^2)
  have hq : x^2-3*B*x+2*B^2-4*A^2 = (x-lower22 A B)*(x-radius22 A B) := by
    unfold lower22 radius22
    nlinarith only [hs]
  rw [matrix22_charpoly, hq, mul_eq_zero, mul_eq_zero,
    add_eq_zero_iff_eq_neg, sub_eq_zero, sub_eq_zero]

theorem matrix22_norm (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ‖kernelOperator (matrix22 A B)‖ = radius22 A B := by
  have hs := Real.sqrt_nonneg (B^2+16*A^2)
  apply norm_eq_of_charpoly_roots (matrix22 A B) (matrix22_symmetric A B)
    (radius22 A B) (by unfold radius22; positivity)
  · intro x hx
    rcases (matrix22_roots A B x).mp hx with h|h|h
    · rw [h, abs_neg, abs_of_nonneg hB]
      unfold radius22
      linarith
    · rw [h]
      unfold lower22 radius22
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [h, abs_of_nonneg (by unfold radius22; positivity)]
  · exact (matrix22_roots A B _).mpr (Or.inr (Or.inr rfl))

/-- First printed subset-array norm; the scalar byte factor stays outside. -/
theorem subset_degree11_norm : ‖kernelOperator (subsetKernel 3 3 degree11)‖ = 3 := by
  rw [subset_norm, compressed11, matrix11_norm]

/-- Second printed subset-array norm, with no frame or byte factors included. -/
theorem subset_degree12_norm : ‖kernelOperator (subsetKernel 3 2 degree12)‖ =
    Real.sqrt (8+2*Real.sqrt 13) := by
  rw [subset_norm, compressed12, matrix12_norm]

/-- Third printed norm for every pair of nonnegative scalar entries. -/
theorem subset_degree22_norm (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ‖kernelOperator (subsetKernel 2 2 (degree22 A B))‖ =
      (3*B+Real.sqrt (B^2+16*A^2))/2 := by
  rw [subset_norm, compressed22, matrix22_norm A B hA hB]
  rfl

end AES8.PaperSubsetArrayNorms
