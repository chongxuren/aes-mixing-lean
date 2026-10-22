import AES8.Math.PaperFiniteSymmetricNorm
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
Literal slope route: similarity and the maximum-row-sum spectral argument.

This source candidate is isolated for formal-node compilation by the owning
root task. It has not been compiled locally. No attacks or external-theorem
proof work are in scope. In particular, no Schur/variational comparison is
used to obtain the spectral bound.
-/

noncomputable section
open scoped BigOperators Matrix ENNReal NNReal

namespace AES8.PaperSlopeLiteral

set_option autoImplicit false

variable {I 𝕜 : Type*} [Fintype I] [DecidableEq I] [RCLike 𝕜]

/-- Conjugation by a matrix with a specified two-sided inverse. The actual
inverse identities, rather than a spectrum-preservation premise, are inputs. -/
def similarity (S R : Matrix I I 𝕜) (hSR : S * R = 1) (hRS : R * S = 1) :
    Matrix I I 𝕜 ≃ₐ[𝕜] Matrix I I 𝕜 where
  toFun A := S * A * R
  invFun A := R * A * S
  left_inv A := by
    simp only [Matrix.mul_assoc, hRS, Matrix.mul_one]
    rw [← Matrix.mul_assoc R S, hRS, Matrix.one_mul]
  right_inv A := by
    simp only [Matrix.mul_assoc, hSR, Matrix.mul_one]
    rw [← Matrix.mul_assoc S R, hSR, Matrix.one_mul]
  map_mul' A B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R S, hRS, Matrix.one_mul]
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  commutes' a := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hSR]

@[simp] theorem similarity_apply (S R : Matrix I I 𝕜)
    (hSR : S * R = 1) (hRS : R * S = 1) (A : Matrix I I 𝕜) :
    similarity S R hSR hRS A = S * A * R := rfl

theorem similarity_spectrum (S R : Matrix I I 𝕜)
    (hSR : S * R = 1) (hRS : R * S = 1) (A : Matrix I I 𝕜) :
    spectrum 𝕜 (S * A * R) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (similarity S R hSR hRS) A

theorem similarity_spectralRadius (S R : Matrix I I 𝕜)
    (hSR : S * R = 1) (hRS : R * S = 1) (A : Matrix I I 𝕜) :
    spectralRadius 𝕜 (S * A * R) = spectralRadius 𝕜 A := by
  unfold spectralRadius
  rw [similarity_spectrum S R hSR hRS]

/-- The diagonal matrices occurring in positive diagonal similarity. -/
def weightDiagonal (w : I → ℝ) : Matrix I I ℝ := Matrix.diagonal w

def inverseWeightDiagonal (w : I → ℝ) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => (w i)⁻¹)

theorem weight_inverse (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    weightDiagonal w * inverseWeightDiagonal w = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weightDiagonal, inverseWeightDiagonal, Matrix.diagonal,
      Matrix.mul_apply, Matrix.one_apply, ne_of_gt (hw i)]
  · simp [weightDiagonal, inverseWeightDiagonal, Matrix.diagonal,
      Matrix.mul_apply, Matrix.one_apply, hij]

theorem inverse_weight (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    inverseWeightDiagonal w * weightDiagonal w = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weightDiagonal, inverseWeightDiagonal, Matrix.diagonal,
      Matrix.mul_apply, Matrix.one_apply, ne_of_gt (hw i)]
  · simp [weightDiagonal, inverseWeightDiagonal, Matrix.diagonal,
      Matrix.mul_apply, Matrix.one_apply, hij]

def weightedSimilar (P : Matrix I I ℝ) (w : I → ℝ) : Matrix I I ℝ :=
  inverseWeightDiagonal w * P * weightDiagonal w

theorem weightedSimilar_apply (P : Matrix I I ℝ) (w : I → ℝ) (i j : I) :
    weightedSimilar P w i j = P i j * w j / w i := by
  simp [weightedSimilar, weightDiagonal, inverseWeightDiagonal,
    Matrix.mul_apply, Matrix.diagonal, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm]

theorem weightedSimilar_nonneg (P : Matrix I I ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (w : I → ℝ) (hw : ∀ i, 0 < w i) (i j : I) :
    0 ≤ weightedSimilar P w i j := by
  rw [weightedSimilar_apply]
  exact div_nonneg (mul_nonneg (hP i j) (hw j).le) (hw i).le

theorem weightedSimilar_rows (P : Matrix I I ℝ) (w : I → ℝ) (i : I) :
    (∑ j, weightedSimilar P w i j) = (P *ᵥ w) i / w i := by
  simp only [weightedSimilar_apply, ← Finset.sum_div, Matrix.mulVec, dotProduct]

theorem weightedSimilar_spectrum (P : Matrix I I ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) :
    spectrum ℝ (weightedSimilar P w) = spectrum ℝ P :=
  similarity_spectrum _ _ (inverse_weight w hw) (weight_inverse w hw) P

theorem weightedSimilar_spectralRadius (P : Matrix I I ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) :
    spectralRadius ℝ (weightedSimilar P w) = spectralRadius ℝ P :=
  similarity_spectralRadius _ _ (inverse_weight w hw) (weight_inverse w hw) P

/-- The maximum-coordinate argument bounds every eigenvalue over either
real or complex scalars by the maximum absolute row sum. -/
theorem eigenvalue_norm_le_rows (A : Matrix I I 𝕜) (r : ℝ)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ r)
    (μ : 𝕜) (v : I → 𝕜) (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) : ‖μ‖ ≤ r := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  letI : Nonempty I := ⟨i₀⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖v j‖) Finset.univ_nonempty
  have hvi : 0 < ‖v i‖ :=
    (norm_pos_iff.mpr hi₀).trans_le (hmax i₀ (Finset.mem_univ i₀))
  have heq : (∑ j, A i j * v j) = μ * v i := congrFun heig i
  have hmul : ‖μ‖ * ‖v i‖ ≤ r * ‖v i‖ := by
    calc
      _ = ‖∑ j, A i j * v j‖ := by rw [heq, norm_mul]
      _ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, ‖A i j‖ * ‖v i‖ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (norm_nonneg _)
      _ = (∑ j, ‖A i j‖) * ‖v i‖ := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  by_contra! h
  exact (not_lt_of_ge hmul) (mul_lt_mul_of_pos_right h hvi)

/-- A finite matrix's spectral values have nonzero eigenvectors, so the
row argument is a bound on its spectrum, rather than on a chosen basis. -/
theorem spectrum_norm_le_rows (A : Matrix I I 𝕜) (r : ℝ)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ r) (μ : 𝕜) (hμ : μ ∈ spectrum 𝕜 A) :
    ‖μ‖ ≤ r := by
  have hlin : μ ∈ spectrum 𝕜 A.toLin' := by
    rwa [Matrix.spectrum_toLin']
  obtain ⟨v, hv⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlin).exists_hasEigenvector
  apply eigenvalue_norm_le_rows A r hrow μ v hv.2
  exact hv.apply_eq_smul

theorem real_spectrum_abs_le_rows (A : Matrix I I ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (r : ℝ) (hrow : ∀ i, (∑ j, A i j) ≤ r)
    (μ : ℝ) (hμ : μ ∈ spectrum ℝ A) : |μ| ≤ r := by
  simpa only [Real.norm_eq_abs] using
    spectrum_norm_le_rows A r (fun i => by
      have hn : (∑ j, ‖A i j‖) = ∑ j, A i j := by
        apply Finset.sum_congr rfl
        intro j _
        exact Real.norm_of_nonneg (hA i j)
      rw [hn]
      exact hrow i) μ hμ

/-- This radius theorem is over either real or complex scalars. Thus the
maximum-row argument is also available for the usual complex radius. -/
theorem spectralRadius_le_rows (A : Matrix I I 𝕜) (r : ℝ≥0)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ (r : ℝ)) :
    spectralRadius 𝕜 A ≤ (r : ℝ≥0∞) := by
  unfold spectralRadius
  refine iSup₂_le fun μ hμ => ?_
  apply ENNReal.coe_le_coe.mpr
  exact_mod_cast spectrum_norm_le_rows A r hrow μ hμ

/-- Uniform strict row sums yield a strict spectral estimate by first
choosing one smaller row maximum. The `a` is retained for operator suprema. -/
theorem exists_row_spectral_margin (A : Matrix I I ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (r : ℝ) (hr : 0 < r)
    (hrow : ∀ i, (∑ j, A i j) < r) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧ ∀ μ ∈ spectrum ℝ A, |μ| ≤ a := by
  classical
  by_cases hI : Nonempty I
  · letI := hI
    obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun i => ∑ j, A i j) Finset.univ_nonempty
    let b := max 0 (∑ j, A i j)
    have hb : b < r := max_lt hr (hrow i)
    have hb0 : 0 ≤ b := le_max_left _ _
    refine ⟨(b+r)/2, by linarith, by linarith, ?_⟩
    intro μ hμ
    apply real_spectrum_abs_le_rows A hA ((b+r)/2) _ μ hμ
    intro j
    exact (hmax j (Finset.mem_univ j)).trans
      ((le_max_right 0 _).trans (by change b ≤ (b+r)/2; linarith))
  · refine ⟨r/2, by linarith, by linarith, ?_⟩
    intro μ hμ
    have hempty : ∀ i, (∑ j, A i j) ≤ r/2 := fun i => (hI ⟨i⟩).elim
    exact real_spectrum_abs_le_rows A hA (r/2) hempty μ hμ

end AES8.PaperSlopeLiteral
