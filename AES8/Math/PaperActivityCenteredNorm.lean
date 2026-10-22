import AES8.Math.PaperActivityOperatorCompression
import AES8.Math.PaperFiniteSymmetricNorm

/-! Centering, spectrum, and exact norm of the generic activity sandwich.
The similarity and eigenvalue-to-norm bridge are proved here. The frozen
spectrum calculations are reused without altering their bytes. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperActivityCenteredNorm
open PaperKernelBounds PaperActivityOperatorCompression PaperActivitySpectrum PaperFiniteSymmetricNorm
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3600000

/-- Total-mass matrix after removing the uniform nonzero direction. -/
def centeredMass (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => massMatrix m a b - mass m a/(m^4-1)

private theorem fourth_sub_one_pos (m : ℝ) (hm : 1 < m) : 0 < m^4-1 := by
  have h2 : 1 < m^2 := by nlinarith
  nlinarith [sq_nonneg (m^2-1)]

theorem centered_conjugation (m : ℝ) (hm : 1 < m) :
    centeredMatrix m = Matrix.diagonal (fun a => (scale m a)⁻¹) *
      centeredMass m * Matrix.diagonal (scale m) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, centeredMass]
  rw [massMatrix_eq_coefficient m hm a b, ← scale_sq m hm a]
  unfold centeredMatrix
  field_simp [ne_of_gt (scale_pos m hm a), ne_of_gt (fourth_sub_one_pos m hm)]
  <;> ring

theorem centered_charpoly_eq (m : ℝ) (hm : 1 < m) :
    (centeredMatrix m).charpoly = (centeredMass m).charpoly := by
  have hd : Matrix.diagonal (scale m) * Matrix.diagonal (fun a => (scale m a)⁻¹) =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    have hh : (fun a : Fin 4 => scale m a*(scale m a)⁻¹) = fun _ => (1 : ℝ) := by
      funext a
      exact mul_inv_cancel₀ (ne_of_gt (scale_pos m hm a))
    rw [hh]
    simp
  rw [centered_conjugation m hm, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hd,
    Matrix.one_mul]

private theorem mass_eq_uniform (n : ℝ) : mass (n+1) = uniformMass n := by
  ext a
  fin_cases a <;> norm_num [mass, AESConcrete.ActivityRankOneStep.activityMass, weight, uniformMass, Nat.choose]
  <;> ring

/-- Rank-one centering replaces precisely the uniform eigenvalue by zero. -/
theorem centered_charpoly_eval (m x : ℝ) (hm : 1 < m) :
    (centeredMatrix m).charpoly.eval x =
      x*(x-4/(m-1)^2)*(x^2+10*(m+1)/(m-1)^3*x+24/(m-1)^4) := by
  rw [centered_charpoly_eq m hm]
  obtain ⟨n, rfl⟩ : ∃ n : ℝ, m = n+1 := ⟨m-1, by ring⟩
  have hn : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hN : (n+1)^4-1 ≠ 0 := ne_of_gt (fourth_sub_one_pos (n+1) hm)
  have hm1 : n+1 ≠ 1 := by linarith
  have hmat : centeredMass (n+1) =
      fun a b => sparseMatrix n a b - uniformMass n a/((n+1)^4-1) := by
    ext a b
    simp only [centeredMass, massMatrix_eq_sparse (n+1) hm1, add_sub_cancel_right,
      mass_eq_uniform]
  rw [hmat, Matrix.eval_charpoly]
  simp [sparseMatrix, uniformMass, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.sub_apply, Fin.sum_univ_succ, Fin.succAbove]
  field_simp [hn0, hN]
  <;> ring

theorem centered_characteristic_roots (m x : ℝ) (hm : 1 < m) :
    (centeredMatrix m).charpoly.eval x = 0 ↔
      x=0 ∨ x=4/(m-1)^2 ∨ x=rootMinus (m-1) ∨ x=rootPlus (m-1) := by
  rw [centered_charpoly_eval m x hm, mul_eq_zero, mul_eq_zero,
    sub_eq_zero]
  have he : 10*(m+1)=10*((m-1)+2) := by ring
  rw [he, quadratic_roots (m-1) x (sub_pos.mpr hm)]
  tauto

/-- Every eigenvalue of the actual symmetric compression is bounded by the
printed radius. Symmetry itself was derived from the exact MDS kernel. -/
theorem centered_eigenvalue_bound (m : ℝ) (hm : 1 < m) (i : Fin 4) :
    |(centered_symmetric m).eigenvalues i| ≤ radius (m-1) := by
  let e := (centered_symmetric m).eigenvalues i
  have hr : (centeredMatrix m).charpoly.eval e = 0 :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      ((centered_symmetric m).eigenvalues_mem_spectrum_real i))
  change |e| ≤ radius (m-1)
  rcases (centered_characteristic_roots m e hm).mp hr with h|h|h|h
  · rw [h, abs_zero]
    exact (lt_trans (div_pos (by norm_num : (0 : ℝ) < 4)
      (pow_pos (sub_pos.mpr hm) 2))
      (second_eigenvalue_lt_radius (m-1) (sub_pos.mpr hm))).le
  · rw [h, abs_of_pos (div_pos (by norm_num) (pow_pos (sub_pos.mpr hm) 2))]
    exact (second_eigenvalue_lt_radius (m-1) (sub_pos.mpr hm)).le
  · rw [h, abs_rootMinus (m-1) (sub_pos.mpr hm)]
  · rw [h]
    exact abs_rootPlus_le (m-1) (sub_pos.mpr hm)

/-- The exact centered compression norm is the printed larger absolute root. -/
theorem centered_matrix_norm (m : ℝ) (hm : 1 < m) :
    ‖kernelOperator (centeredMatrix m)‖ = radius (m-1) := by
  have hr : 0 ≤ radius (m-1) := by
    rw [← abs_rootMinus (m-1) (sub_pos.mpr hm)]
    exact abs_nonneg _
  apply le_antisymm
  · exact norm_le_eigenvalue_bound (centeredMatrix m) (centered_symmetric m)
      (radius (m-1)) hr (centered_eigenvalue_bound m hm)
  · have hroot : (centeredMatrix m).charpoly.IsRoot (rootMinus (m-1)) :=
      (centered_characteristic_roots m (rootMinus (m-1)) hm).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hs := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    rw [(centered_symmetric m).spectrum_real_eq_range_eigenvalues] at hs
    obtain ⟨i, hi⟩ := hs
    rw [← abs_rootMinus (m-1) (sub_pos.mpr hm), ← hi]
    exact abs_eigenvalue_le_norm (centeredMatrix m) (centered_symmetric m) i

/-- The trace follows from the actual weighted entries, without a spectral
multiplicity premise. -/
theorem centered_matrix_trace (m : ℝ) (hm : 1 < m) :
    Matrix.trace (centeredMatrix m^2) = (68*m^2+264*m+68)/(m-1)^6 := by
  have hs : ∀ a b : Fin 4, centeredMatrix m b a = centeredMatrix m a b := by
    intro a b
    have h := congrFun (congrFun (centered_symmetric m) a) b
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have he : Matrix.trace (centeredMatrix m^2) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (coefficient m a b-1/(m^4-1))^2 * mass m a * mass m b := by
    simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hs a b, ← pow_two]
    simp only [centeredMatrix, mul_pow, scale_sq m hm]
    ring
  rw [he]
  have hn0 : m-1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  have hN : m^4-1 ≠ 0 := ne_of_gt (fourth_sub_one_pos m hm)
  norm_num [coefficient, mass, AESConcrete.ActivityRankOneStep.activityMass, weight,
    AESPaper.ActivityMDSCounts.supportCount, Fin.sum_univ_succ, Finset.sum_range_succ,
    Nat.choose]
  field_simp [hn0, hN]
  <;> ring

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The exact norm of the actual centered activity sandwich, at every admissible
alphabet size and for every additive four-coordinate MDS map. -/
theorem actual_activity_norm (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : AESMixing.ZeroMDS L) :
    ‖kernelOperator (centeredKernel L)‖ =
      (5*((Fintype.card V : ℝ)+1)+Real.sqrt
        ((Fintype.card V : ℝ)^2+98*(Fintype.card V : ℝ)+1))/
          ((Fintype.card V : ℝ)-1)^3 := by
  rw [centered_norm_transfer hn L hL, centered_matrix_norm (Fintype.card V)
    (by exact_mod_cast hn), radius_paper]

/-- The actual Hilbert--Schmidt energy has the paper's exact generic formula. -/
theorem actual_activity_hs (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : AESMixing.ZeroMDS L) :
    (∑ y : Fin 4 → V, ∑ x : Fin 4 → V, centeredKernel L y x ^ 2) =
      (68*(Fintype.card V : ℝ)^2+264*(Fintype.card V : ℝ)+68)/
        ((Fintype.card V : ℝ)-1)^6 := by
  rw [centered_trace_transfer hn L hL, centered_matrix_trace (Fintype.card V)
    (by exact_mod_cast hn)]

end AES8.PaperActivityCenteredNorm
