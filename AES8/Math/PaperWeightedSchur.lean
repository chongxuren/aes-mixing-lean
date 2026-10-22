/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-!
# The paper's weighted Schur bound

This module formalizes Lemma 4 (`lem:schur`) of the authoritative manuscript's
`writing/sections/03-gram.tex`. Scalars and weights are real, as fixed at the
start of that section; weights need not be nonnegative or normalized.

`schurProduct` is a finite entrywise product, with the all-ones matrix as its
empty product. `weighted_schur_bound_finite` has an arbitrary finite family of
PSD matrices, a distinguished first factor, and the manuscript's Loewner
premise. Thus it covers every `j ≥ 2` without fixing any numerical parameters.

The proof first derives the finite real Schur product theorem from Hermitian
spectral diagonalization and PSD congruences. It then applies that theorem to
the PSD difference `nu² I - G₁` and expands its quadratic form. No Gram
factorization, desired inequality, or AES numerical estimate is assumed. The
proof avoids the matrix-order and C-star functional-calculus imports.
Constructive proof development only; no attacks, manuscript edits, or
predecessor edits.
-/

noncomputable section

open scoped BigOperators

namespace AES8.PaperWeightedSchur

variable {I J : Type*} [Fintype I] [DecidableEq I]

/-- A finite entrywise matrix product. Its empty product is the all-ones matrix,
not the identity matrix for ordinary matrix multiplication. -/
def schurProduct (G : J → Matrix I I ℝ) (s : Finset J) : Matrix I I ℝ :=
  fun x y => s.prod (fun j => G j x y)

/-- The real quadratic form `muᵀ M mu`, written as finite coordinate sums. -/
def quadratic (M : Matrix I I ℝ) (mu : I → ℝ) : ℝ :=
  ∑ x, ∑ y, mu x * M x y * mu y

/-- Finite real Schur product positivity, proved using spectral diagonalization
and PSD congruence. This keeps the arbitrary-PSD interface without importing
the matrix-order/C-star functional-calculus development. -/
theorem hadamard_posSemidef {A B : Matrix I I ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (Matrix.hadamard A B).PosSemidef := by
  classical
  let U : Matrix I I ℝ := hB.isHermitian.eigenvectorUnitary
  let eigenvalue : I → ℝ := hB.isHermitian.eigenvalues
  have heigenvalue (k : I) : 0 ≤ eigenvalue k := by
    dsimp only [eigenvalue]
    rw [hB.isHermitian.eigenvalues_eq k]
    simpa using hB.dotProduct_mulVec_nonneg ⇑(hB.isHermitian.eigenvectorBasis k)
  have hentry (x y : I) : B x y = ∑ k, U x k * eigenvalue k * U y k := by
    have h := congrArg (fun M : Matrix I I ℝ => M x y) hB.isHermitian.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, U, eigenvalue] using h
  have hterm (k : I) :
      (eigenvalue k • (Matrix.diagonal (fun x => U x k) * A *
        Matrix.diagonal (fun x => U x k))).PosSemidef := by
    apply Matrix.PosSemidef.smul _ (heigenvalue k)
    simpa only [Matrix.diagonal_conjTranspose, star_trivial] using
      hA.conjTranspose_mul_mul_same (Matrix.diagonal (fun x => U x k))
  have hsum :
      (∑ k, eigenvalue k • (Matrix.diagonal (fun x => U x k) * A *
        Matrix.diagonal (fun x => U x k))).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun k _ => hterm k)
  have hmatrix : Matrix.hadamard A B =
      ∑ k, eigenvalue k • (Matrix.diagonal (fun x => U x k) * A *
        Matrix.diagonal (fun x => U x k)) := by
    funext x y
    simp only [Matrix.hadamard_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hentry x y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Matrix.mul_apply, Matrix.diagonal, mul_assoc, mul_left_comm, mul_comm]
  rw [hmatrix]
  exact hsum

/-- The Schur product theorem extends to every finite number of factors. -/
theorem schurProduct_posSemidef (G : J → Matrix I I ℝ) (s : Finset J)
    (hG : ∀ j ∈ s, (G j).PosSemidef) : (schurProduct G s).PosSemidef := by
  classical
  revert hG
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have hempty : schurProduct G (∅ : Finset J) =
          Matrix.vecMulVec (fun _ : I => (1 : ℝ)) (star (fun _ : I => (1 : ℝ))) := by
        funext x y
        simp [schurProduct, Matrix.vecMulVec, Matrix.of]
        rfl
      rw [hempty]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℝ))
  | @insert j s hjs ih =>
      intro hG
      have hs : (schurProduct G s).PosSemidef :=
        ih (fun k hk => hG k (Finset.mem_insert_of_mem hk))
      have heq : schurProduct G (insert j s) =
          Matrix.hadamard (G j) (schurProduct G s) := by
        funext x y
        simp only [schurProduct, Finset.prod_insert hjs, Matrix.hadamard_apply]
      rw [heq]
      exact hadamard_posSemidef (hG j (Finset.mem_insert_self j s)) hs

theorem quadratic_nonneg {M : Matrix I I ℝ} (hM : M.PosSemidef) (mu : I → ℝ) :
    0 ≤ quadratic M mu := by
  simpa [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    hM.dotProduct_mulVec_nonneg mu

theorem quadratic_sub (A B : Matrix I I ℝ) (mu : I → ℝ) :
    quadratic (A - B) mu = quadratic A mu - quadratic B mu := by
  simp only [quadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem quadratic_diagonal (d mu : I → ℝ) :
    quadratic (Matrix.diagonal d) mu = ∑ x, mu x ^ 2 * d x := by
  simp [quadratic, Matrix.diagonal, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Schur multiplication preserves the Loewner upper bound, with arbitrary
signed real weights. The first factor itself need not be PSD for this stronger
intermediate statement; positivity of the difference is the premise used. -/
theorem weighted_schur_bound_two (A H : Matrix I I ℝ) (mu : I → ℝ) (c : ℝ)
    (hH : H.PosSemidef) (hOrder : (c • (1 : Matrix I I ℝ) - A).PosSemidef) :
    quadratic (Matrix.hadamard A H) mu ≤ c * ∑ x, mu x ^ 2 * H x x := by
  classical
  have hnonneg := quadratic_nonneg (hadamard_posSemidef hOrder hH) mu
  have hmatrix : Matrix.hadamard (c • (1 : Matrix I I ℝ) - A) H =
      Matrix.diagonal (fun x => c * H x x) - Matrix.hadamard A H := by
    funext x y
    by_cases hxy : x = y
    · subst y
      simp [Matrix.hadamard_apply, sub_mul]
    · simp [Matrix.hadamard_apply, Matrix.diagonal, Matrix.one_apply, hxy]
  rw [hmatrix, quadratic_sub, quadratic_diagonal] at hnonneg
  have hsum : (∑ x, mu x ^ 2 * (c * H x x)) =
      c * ∑ x, mu x ^ 2 * H x x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Finite-tail form of the manuscript's weighted Schur bound. The finite set
indexes all factors after the distinguished first matrix. -/
theorem weighted_schur_bound (A : Matrix I I ℝ) (G : J → Matrix I I ℝ)
    (s : Finset J) (mu : I → ℝ) (nu : ℝ)
    (hG : ∀ j ∈ s, (G j).PosSemidef)
    (hOrder : (nu ^ 2 • (1 : Matrix I I ℝ) - A).PosSemidef) :
    quadratic (Matrix.hadamard A (schurProduct G s)) mu ≤
      nu ^ 2 * ∑ x, |mu x| ^ 2 * s.prod (fun j => G j x x) := by
  simpa only [sq_abs, schurProduct] using
    weighted_schur_bound_two A (schurProduct G s) mu (nu ^ 2)
      (schurProduct_posSemidef G s hG) hOrder

/-- Lemma 4 (`lem:schur`), for a full arbitrary finite family. Take `J = Fin j`
and `first = 0` for the manuscript's `G₁,...,Gⱼ`, where `j ≥ 2`. The theorem
also holds for the one-factor family. `hG` states PSD for every input matrix;
`hOrder` is exactly `G₁ ≼ nu² I`. -/
theorem weighted_schur_bound_finite [Fintype J] [DecidableEq J]
    (G : J → Matrix I I ℝ) (first : J) (mu : I → ℝ) (nu : ℝ)
    (hG : ∀ j, (G j).PosSemidef)
    (hOrder : (nu ^ 2 • (1 : Matrix I I ℝ) - G first).PosSemidef) :
    quadratic (schurProduct G Finset.univ) mu ≤
      nu ^ 2 * ∑ x, |mu x| ^ 2 *
        (Finset.univ.erase first).prod (fun j => G j x x) := by
  have hproduct :
      Matrix.hadamard (G first) (schurProduct G (Finset.univ.erase first)) =
        schurProduct G Finset.univ := by
    funext x y
    exact Finset.mul_prod_erase Finset.univ (fun j => G j x y)
      (Finset.mem_univ first)
  simpa only [hproduct] using
    weighted_schur_bound (G first) G (Finset.univ.erase first) mu nu
      (fun j _ => hG j) hOrder

end AES8.PaperWeightedSchur
