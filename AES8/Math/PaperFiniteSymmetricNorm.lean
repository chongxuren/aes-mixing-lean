import AES8.Math.PaperKernelBounds
import Mathlib.Analysis.Matrix.Spectrum

/-! A reusable finite symmetric spectrum-to-Euclidean-norm bridge.
Independent of activity models, MDS maps, or numerical tables. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperFiniteSymmetricNorm
open PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Coordinate action on the chosen orthonormal eigenbasis. -/
theorem eigenbasis_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (v : EuclideanSpace ℝ I) (i : I) :
    hA.eigenvectorBasis.repr (kernelOperator A v) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr v i := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (hA.eigenvectorBasis i) v
  change inner ℝ (kernelOperator A (hA.eigenvectorBasis i)) v =
    inner ℝ (hA.eigenvectorBasis i) (kernelOperator A v) at hs
  rw [← hs]
  have hv : kernelOperator A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext x
    exact congrFun (hA.mulVec_eigenvectorBasis i) x
  rw [hv, real_inner_smul_left]

/-- A finite symmetric spectral bound implies the actual Euclidean operator
norm bound, proved using its orthonormal eigenbasis. -/
theorem norm_le_eigenvalue_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i : I, |hA.eigenvalues i| ≤ r) : ‖kernelOperator A‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro v
  have he : ‖kernelOperator A v‖^2 ≤ (r*‖v‖)^2 := by
    calc
      _ = ∑ i : I, (hA.eigenvalues i)^2 * (hA.eigenvectorBasis.repr v i)^2 := by
        rw [← hA.eigenvectorBasis.repr.norm_map (kernelOperator A v), EuclideanSpace.norm_sq_eq]
        simp only [eigenbasis_coordinates A hA, Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ∑ i : I, r^2 * (hA.eigenvectorBasis.repr v i)^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr (h i)
      _ = _ := by
        rw [← Finset.mul_sum]
        have hv := EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis.repr v)
        simp only [Real.norm_eq_abs, sq_abs, hA.eigenvectorBasis.repr.norm_map] at hv
        rw [← hv, mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp he

/-- Every genuine eigenvalue gives the matching lower norm bound. -/
theorem abs_eigenvalue_le_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (i : I) :
    |hA.eigenvalues i| ≤ ‖kernelOperator A‖ := by
  have hv : kernelOperator A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext x
    exact congrFun (hA.mulVec_eigenvectorBasis i) x
  have h := (kernelOperator A).le_opNorm (hA.eigenvectorBasis i)
  simpa only [hv, norm_smul, Real.norm_eq_abs, hA.eigenvectorBasis.norm_eq_one, mul_one] using h


end AES8.PaperFiniteSymmetricNorm
