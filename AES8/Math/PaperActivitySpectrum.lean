import AESPaper.ActivityMDSCounts
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Tauto

/-! The printed generic four-weight activity spectrum calculation.
`massMatrix` uses the existing exact MDS graph-support counts. This leaf proves
the finite matrix algebra and scalar root calculations only; correspondence
with activity compression and its operator norm is a separate interface.
Constructive mathematics only; no attacks or concrete-only replacement.
-/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperActivitySpectrum
open Polynomial
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Total-mass coordinates at nonzero support weights one through four. -/
def massMatrix (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => (Nat.choose 4 (a.val+1) : ℝ) *
    AESPaper.ActivityMDSCounts.supportCount m (a.val+b.val+2)/(m-1)^(b.val+1)

/-- The same matrix with `n=m-1`, after substituting the exact support counts. -/
def sparseMatrix (n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 4/n^3;
     0, 0, 6/n^2, 6*(n-4)/n^3;
     0, 4/n, 4*(n-4)/n^2, 4*(n^2-4*n+10)/n^3;
     1, (n-4)/n, (n^2-4*n+10)/n^2, (n^3-4*n^2+10*n-20)/n^3]

theorem massMatrix_eq_sparse (m : ℝ) (hm : m ≠ 1) :
    massMatrix m = sparseMatrix (m-1) := by
  have hn : m-1 ≠ 0 := sub_ne_zero.mpr hm
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [massMatrix, sparseMatrix, AESPaper.ActivityMDSCounts.supportCount,
      Finset.sum_range_succ, Nat.choose] <;> field_simp [hn] <;> ring

/-- Unnormalized mass of the uniform nonzero distribution at each weight. -/
def uniformMass (n : ℝ) : Fin 4 → ℝ := ![4*n, 6*n^2, 4*n^3, n^4]

/-- The second eigenvector printed in the paper, in the parameter `n=m-1`. -/
def secondVector (n : ℝ) : Fin 4 → ℝ := ![1, -3, 2-n, n]

theorem uniformMass_ne_zero (n : ℝ) (hn : n ≠ 0) : uniformMass n ≠ 0 := by
  intro h
  have hh := congrFun h 0
  have : 4*n=0 := by simpa [uniformMass] using hh
  exact hn ((mul_eq_zero.mp this).resolve_left (by norm_num))

theorem secondVector_ne_zero (n : ℝ) : secondVector n ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [secondVector] at hh

theorem uniform_eigenvector (n : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).mulVec (uniformMass n) = uniformMass n := by
  ext i
  fin_cases i <;>
    simp [sparseMatrix, uniformMass, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hn] <;> ring

theorem second_eigenvector (n : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).mulVec (secondVector n) = (4/n^2) • secondVector n := by
  ext i
  fin_cases i <;>
    simp [sparseMatrix, secondVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hn] <;> ring

theorem secondVector_centered (n : ℝ) : (∑ i, secondVector n i) = 0 := by
  simp [secondVector, Fin.sum_univ_succ]
  ring

theorem uniformMass_sum (n : ℝ) : (∑ i, uniformMass n i) = (n+1)^4-1 := by
  simp [uniformMass, Fin.sum_univ_succ]
  ring

/-- The sparse anti-triangular determinant in the printed argument. -/
theorem determinant (n : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).det = 96/n^6 := by
  simp [sparseMatrix, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]
  field_simp [hn]
  ring

theorem trace (n : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).trace = 1-6/n^2-20/n^3 := by
  simp [Matrix.trace, Matrix.diag_apply, sparseMatrix, Fin.sum_univ_succ]
  field_simp [hn]
  ring

/-- The two remaining eigenvalues have this quadratic factor. -/
def residualPolynomial (n : ℝ) : ℝ[X] :=
  X^2+C (10*(n+2)/n^3)*X+C (24/n^4)

theorem charpoly_eval (n x : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).charpoly.eval x =
      (x-1)*(x-4/n^2)*(x^2+(10*(n+2)/n^3)*x+24/n^4) := by
  rw [Matrix.eval_charpoly]
  simp [sparseMatrix, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply, Fin.sum_univ_succ, Fin.succAbove]
  field_simp [hn]
  ring

theorem charpoly_factor (n : ℝ) (hn : n ≠ 0) :
    (sparseMatrix n).charpoly =
      (X-C 1)*(X-C (4/n^2))*residualPolynomial n := by
  apply Polynomial.funext
  intro x
  simpa [residualPolynomial] using charpoly_eval n x hn

/-- Negative quadratic root of larger magnitude. -/
def rootMinus (n : ℝ) : ℝ :=
  (-5*(n+2)-Real.sqrt (n^2+100*n+100))/n^3

def rootPlus (n : ℝ) : ℝ :=
  (-5*(n+2)+Real.sqrt (n^2+100*n+100))/n^3

theorem discriminant_nonneg (n : ℝ) (hn : 0 < n) : 0 ≤ n^2+100*n+100 := by
  positivity

theorem root_sum (n : ℝ) :
    rootMinus n+rootPlus n = -10*(n+2)/n^3 := by
  unfold rootMinus rootPlus
  ring

theorem root_product (n : ℝ) (hn : 0 < n) :
    rootMinus n*rootPlus n = 24/n^4 := by
  have hs := Real.sq_sqrt (discriminant_nonneg n hn)
  unfold rootMinus rootPlus
  have hn0 := ne_of_gt hn
  field_simp [hn0]
  ring_nf at hs ⊢
  nlinarith only [hs]

theorem quadratic_factor (n x : ℝ) (hn : 0 < n) :
    x^2+(10*(n+2)/n^3)*x+24/n^4 = (x-rootMinus n)*(x-rootPlus n) := by
  rw [show (x-rootMinus n)*(x-rootPlus n) =
    x^2-(rootMinus n+rootPlus n)*x+rootMinus n*rootPlus n by ring,
    root_sum, root_product n hn]
  ring

theorem quadratic_roots (n x : ℝ) (hn : 0 < n) :
    x^2+(10*(n+2)/n^3)*x+24/n^4=0 ↔ x=rootMinus n ∨ x=rootPlus n := by
  rw [quadratic_factor n x hn, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem characteristic_roots (n x : ℝ) (hn : 0 < n) :
    (sparseMatrix n).charpoly.eval x=0 ↔
      x=1 ∨ x=4/n^2 ∨ x=rootMinus n ∨ x=rootPlus n := by
  rw [charpoly_eval n x (ne_of_gt hn), mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, quadratic_roots n x hn]
  tauto

theorem rootPlus_negative (n : ℝ) (hn : 0 < n) : rootPlus n < 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg n hn)
  have hsq := Real.sqrt_nonneg (n^2+100*n+100)
  have hlt : Real.sqrt (n^2+100*n+100) < 5*(n+2) := by nlinarith
  unfold rootPlus
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos hn 3)

theorem rootMinus_negative (n : ℝ) (hn : 0 < n) : rootMinus n < 0 := by
  have hs := Real.sqrt_nonneg (n^2+100*n+100)
  unfold rootMinus
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos hn 3)

/-- The magnitude expression used for the centered norm in the paper. -/
def radius (n : ℝ) : ℝ :=
  (5*(n+2)+Real.sqrt (n^2+100*n+100))/n^3

theorem abs_rootMinus (n : ℝ) (hn : 0 < n) : |rootMinus n| = radius n := by
  rw [abs_of_neg (rootMinus_negative n hn)]
  unfold rootMinus radius
  ring

theorem abs_rootPlus_le (n : ℝ) (hn : 0 < n) : |rootPlus n| ≤ radius n := by
  rw [abs_of_neg (rootPlus_negative n hn)]
  unfold rootPlus radius
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le 3)
  have hs := Real.sqrt_nonneg (n^2+100*n+100)
  linarith

theorem second_eigenvalue_lt_radius (n : ℝ) (hn : 0 < n) : 4/n^2 < radius n := by
  have hn0 := ne_of_gt hn
  have he : 4/n^2=(4*n)/n^3 := by field_simp [hn0]
  rw [he]
  unfold radius
  apply (div_lt_div_iff_of_pos_right (pow_pos hn 3)).mpr
  have hs := Real.sqrt_nonneg (n^2+100*n+100)
  linarith

theorem radius_upper (n : ℝ) (hn : 0 < n) : radius n < (6*n+60)/n^3 := by
  have hs := Real.sq_sqrt (discriminant_nonneg n hn)
  have hsq := Real.sqrt_nonneg (n^2+100*n+100)
  have hlt : Real.sqrt (n^2+100*n+100) < n+50 := by nlinarith
  unfold radius
  apply (div_lt_div_iff_of_pos_right (pow_pos hn 3)).mpr
  linarith

/-- The sum of the squares of the three centered eigenvalues. -/
theorem centered_square_sum (n : ℝ) (hn : 0 < n) :
    (4/n^2)^2+(rootMinus n)^2+(rootPlus n)^2 =
      (68*(n+1)^2+264*(n+1)+68)/n^6 := by
  have he : (rootMinus n)^2+(rootPlus n)^2 =
      (rootMinus n+rootPlus n)^2-2*(rootMinus n*rootPlus n) := by ring
  rw [show (4/n^2)^2+(rootMinus n)^2+(rootPlus n)^2 =
    (4/n^2)^2+((rootMinus n)^2+(rootPlus n)^2) by ring,
    he, root_sum, root_product n hn]
  have hn0 := ne_of_gt hn
  field_simp [hn0]
  ring

/-- The stated eigenvector at the paper's alphabet parameter. -/
theorem mass_second_eigenvector (m : ℝ) (hm : m ≠ 1) :
    (massMatrix m).mulVec (![1, -3, 3-m, m-1] : Fin 4 → ℝ) =
      (4/(m-1)^2) • (![1, -3, 3-m, m-1] : Fin 4 → ℝ) := by
  have hv : secondVector (m-1) = (![1, -3, 3-m, m-1] : Fin 4 → ℝ) := by
    ext i
    fin_cases i <;> simp [secondVector] <;> ring
  rw [massMatrix_eq_sparse m hm, ← hv]
  exact second_eigenvector (m-1) (sub_ne_zero.mpr hm)

theorem mass_determinant (m : ℝ) (hm : m ≠ 1) :
    (massMatrix m).det = 96/(m-1)^6 := by
  rw [massMatrix_eq_sparse m hm]
  exact determinant (m-1) (sub_ne_zero.mpr hm)

theorem mass_trace (m : ℝ) (hm : m ≠ 1) :
    (massMatrix m).trace = 1-6/(m-1)^2-20/(m-1)^3 := by
  rw [massMatrix_eq_sparse m hm]
  exact trace (m-1) (sub_ne_zero.mpr hm)

theorem mass_charpoly_eval (m x : ℝ) (hm : m ≠ 1) :
    (massMatrix m).charpoly.eval x =
      (x-1)*(x-4/(m-1)^2)*(x^2+(10*(m+1)/(m-1)^3)*x+24/(m-1)^4) := by
  rw [massMatrix_eq_sparse m hm, charpoly_eval (m-1) x (sub_ne_zero.mpr hm)]
  congr 2
  ring

/-- Exact expression displayed for the centered radius, before compression
correspondence identifies it with an operator norm. -/
theorem radius_paper (m : ℝ) :
    radius (m-1) =
      (5*(m+1)+Real.sqrt (m^2+98*m+1))/(m-1)^3 := by
  have he : (m-1)^2+100*(m-1)+100=m^2+98*m+1 := by ring
  unfold radius
  rw [he]
  congr 1
  ring

theorem radius_paper_upper (m : ℝ) (hm : 1 < m) :
    (5*(m+1)+Real.sqrt (m^2+98*m+1))/(m-1)^3 <
      (6*m+54)/(m-1)^3 := by
  have he : 6*(m-1)+60=6*m+54 := by ring
  simpa only [radius_paper, he] using radius_upper (m-1) (sub_pos.mpr hm)

theorem centered_square_sum_paper (m : ℝ) (hm : 1 < m) :
    (4/(m-1)^2)^2+(rootMinus (m-1))^2+(rootPlus (m-1))^2 =
      (68*m^2+264*m+68)/(m-1)^6 := by
  simpa only [sub_add_cancel] using centered_square_sum (m-1) (sub_pos.mpr hm)

end AES8.PaperActivitySpectrum
