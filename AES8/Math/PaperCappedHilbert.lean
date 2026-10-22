import AES8.Math.PaperEncodingHilbert
import AESPaper.CappedSourceGram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A capped common source with unequal Hilbert response spaces

The shared label is retained in every tensor factor. This leaf transports the
proved scalar Gram-product estimate to the literal dependent Hilbert tensor;
the local outputs may have different finite dimensions. The Gram matrix is
derived from the actual operators, and its squared-entry sum is identified
with the trace of its square. No probability normalization is assumed.

Frozen paper f902bb94, `cor:capped-source`. This is reusable real Hilbert
mathematics, independent of the concrete AES resource tables.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace AES8.PaperCappedHilbert

open PaperEncodingHilbert

variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
variable {H : K → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℝ (H i)] [∀ i, FiniteDimensional ℝ (H i)]

/-- The actual Gram entries of the local column responses. -/
def gramMatrix (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (i : K) : Matrix V V ℝ :=
  fun x y => inner ℝ (A i (PaperEncoding.basisVector x))
    (A i (PaperEncoding.basisVector y))

/-- These entries are the coefficients of the operator `A† A`. -/
theorem gramMatrix_adjoint (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i)
    (i : K) (x y : V) :
    gramMatrix A i x y = inner ℝ (PaperEncoding.basisVector x)
      ((A i).adjoint (A i (PaperEncoding.basisVector y))) := by
  exact (ContinuousLinearMap.adjoint_inner_right (A i) _ _).symm

theorem gramMatrix_symmetric (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i)
    (i : K) (x y : V) : gramMatrix A i x y = gramMatrix A i y x :=
  real_inner_comm _ _

@[simp] theorem gramMatrix_diagonal (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i)
    (i : K) (x : V) :
    gramMatrix A i x x = ‖A i (PaperEncoding.basisVector x)‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- Symmetry identifies the paper's second Gram moment exactly. -/
theorem gramMatrix_moment (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (i : K) :
    (∑ x, ∑ y, gramMatrix A i x y ^ 2) = Matrix.trace (gramMatrix A i ^ 2) := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [gramMatrix_symmetric A i y x]

/-- Literal common-source tensor response; weights may be signed. -/
def response (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (mu : V → ℝ) :
    HilbertTensor H :=
  ∑ x, mu x • PiTensorProduct.tprod ℝ (fun i => A i (PaperEncoding.basisVector x))

/-- No coordinate embedding or response identity is assumed in the estimate. -/
theorem response_energy (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (mu : V → ℝ) :
    ‖response A mu‖ ^ 2 =
      ∑ x, ∑ y, mu x * mu y * ∏ i, gramMatrix A i x y := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [response, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_tprod, gramMatrix]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [real_inner_comm (A _ (PaperEncoding.basisVector y))
    (A _ (PaperEncoding.basisVector x))]
  ring

theorem gramMatrix_entry_bound (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i)
    (delta : ℝ) (hdiag : ∀ i x, gramMatrix A i x x ≤ delta)
    (i : K) (x y : V) : |gramMatrix A i x y| ≤ delta := by
  have hx := hdiag i x
  have hy := hdiag i y
  rw [gramMatrix_diagonal] at hx hy
  have hcs := abs_real_inner_le_norm (A i (PaperEncoding.basisVector x))
    (A i (PaperEncoding.basisVector y))
  change |gramMatrix A i x y| ≤ _ at hcs
  nlinarith [sq_nonneg (‖A i (PaperEncoding.basisVector x)‖ -
    ‖A i (PaperEncoding.basisVector y)‖)]

/-- Explicit-sign form, also allowing an empty label type. -/
theorem capped_source_energy (n : ℕ)
    {H : Fin (n + 2) → Type*} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℝ (H i)] [∀ i, FiniteDimensional ℝ (H i)]
    (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (mu : V → ℝ)
    (p tau delta : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hdiag : ∀ i x, gramMatrix A i x x ≤ delta)
    (hmoment : ∀ i, Matrix.trace (gramMatrix A i ^ 2) ≤ tau ^ 2) :
    ‖response A mu‖ ^ 2 ≤ p ^ 2 * tau ^ 2 * delta ^ n := by
  rw [response_energy]
  exact AESPaper.CappedSourceGram.weighted_product_bound n (fun i => gramMatrix A i)
    mu p tau delta hp hd hmu (gramMatrix_entry_bound A delta hdiag)
    (fun i => (gramMatrix_moment A i).trans_le (hmoment i))

/-- The paper corollary for every `j ≥ 2`, with arbitrary unequal finite
real Hilbert outputs. The signs of the caps follow from the stated premises. -/
theorem paper_capped_source [Nonempty V] (j : ℕ) (hj : 2 ≤ j)
    {H : Fin j → Type*} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℝ (H i)] [∀ i, FiniteDimensional ℝ (H i)]
    (A : ∀ i, EuclideanSpace ℝ V →L[ℝ] H i) (mu : V → ℝ)
    (p tau delta : ℝ) (hmu : ∀ x, |mu x| ≤ p)
    (hdiag : ∀ i x, gramMatrix A i x x ≤ delta)
    (hmoment : ∀ i, Matrix.trace (gramMatrix A i ^ 2) ≤ tau ^ 2) :
    ‖response A mu‖ ^ 2 ≤ p ^ 2 * tau ^ 2 * delta ^ (j - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  let x : V := Classical.arbitrary V
  have hp : 0 ≤ p := (abs_nonneg (mu x)).trans (hmu x)
  have hd : 0 ≤ delta := by
    have h := hdiag (0 : Fin (n + 2)) x
    rw [gramMatrix_diagonal] at h
    exact (sq_nonneg _).trans h
  simpa using capped_source_energy n A mu p tau delta hp hd hmu hdiag hmoment

end AES8.PaperCappedHilbert
