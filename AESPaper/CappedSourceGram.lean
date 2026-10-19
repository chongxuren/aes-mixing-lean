import AESConcrete.WordColumnGram
import Mathlib.Algebra.BigOperators.Fin

/-!
# Capped common sources and the second Gram moment

The source label is shared by every response factor. After the exact Gram
expansion, two factors are retained in the sum and bounded by Cauchy--Schwarz;
only the remaining factors use the uniform column-energy cap. The result is
`p^2 * tau^2 * delta^(j-2)`, without replacing the second Gram moment by a
norm-times-trace estimate. Signed real source weights are allowed.

The width is `n+2`, so the two retained positions and the `n` remaining
positions have explicit finite indices. The final wrapper applies the frozen
`WordColumnGram.tensorResponse_energy` identity to actual source-coordinate
permutations; these permutations relabel source pairs and need not preserve
the Gram entrywise. No independence among current coordinates is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.CappedSourceGram
open AESMixing

section Scalar
variable {X : Type*} [Fintype X]

/-- Cauchy--Schwarz retains the two complete squared-entry sums. The matrices
may differ; no equality or entrywise invariance of their Grams is required. -/
theorem two_factor_moment (A B : X → X → ℝ) (tau : ℝ)
    (hA : (∑ x, ∑ z, A x z ^ 2) ≤ tau ^ 2)
    (hB : (∑ x, ∑ z, B x z ^ 2) ≤ tau ^ 2) :
    (∑ x, ∑ z, |A x z| * |B x z|) ≤ tau ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun v : X × X => |A v.1 v.2|) (fun v : X × X => |B v.1 v.2|)
  simp only [Fintype.sum_prod_type, sq_abs] at hcs
  have hprod : (∑ x, ∑ z, A x z ^ 2) * (∑ x, ∑ z, B x z ^ 2) ≤
      tau ^ 2 * tau ^ 2 :=
    mul_le_mul hA hB
      (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun z _ => sq_nonneg (B x z))))
      (sq_nonneg tau)
  apply (sq_le_sq₀
    (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun z _ =>
      mul_nonneg (abs_nonneg (A x z)) (abs_nonneg (B x z)))))
    (sq_nonneg tau)).mp
  exact hcs.trans (by simpa only [pow_two] using hprod)

/-- Bound only the tail of a finite product, retaining the first two factors. -/
theorem product_tail_bound (n : ℕ) (f : Fin (n+2) → ℝ) (delta : ℝ)
    (hd : 0 ≤ delta) (hf : ∀ i, |f i| ≤ delta) :
    |∏ i, f i| ≤ |f 0| * |f ((0 : Fin (n+1)).succ)| * delta ^ n := by
  have ht : (∏ i : Fin n, |f i.succ.succ|) ≤ delta ^ n := by
    calc
      _ ≤ ∏ _ : Fin n, delta :=
        Finset.prod_le_prod (fun i _ => abs_nonneg (f i.succ.succ))
          (fun i _ => hf i.succ.succ)
      _ = delta ^ n := by simp
  calc
    _ = |f 0| * |f ((0 : Fin (n+1)).succ)| *
        ∏ i : Fin n, |f i.succ.succ| := by
      rw [Finset.abs_prod, Fin.prod_univ_succ, Fin.prod_univ_succ]
      ring
    _ ≤ |f 0| * |f ((0 : Fin (n+1)).succ)| * delta ^ n :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The signed scalar Gram expansion for one common capped source. This
lemma uses entry and moment bounds explicitly; Gram origin is supplied below. -/
theorem weighted_product_bound (n : ℕ) (G : Fin (n+2) → X → X → ℝ)
    (mu : X → ℝ) (p tau delta : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i x z, |G i x z| ≤ delta)
    (hmoment : ∀ i, (∑ x, ∑ z, G i x z ^ 2) ≤ tau ^ 2) :
    (∑ x, ∑ z, mu x * mu z * ∏ i, G i x z) ≤ p ^ 2 * tau ^ 2 * delta ^ n := by
  have hpair (x z : X) : |mu x * mu z| ≤ p ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ p*p := mul_le_mul (hmu x) (hmu z) (abs_nonneg (mu z)) hp
      _ = p ^ 2 := by ring
  have hpoint (x z : X) : mu x * mu z * (∏ i, G i x z) ≤
      (p ^ 2 * delta ^ n) * (|G 0 x z| * |G ((0 : Fin (n+1)).succ) x z|) := by
    calc
      _ ≤ |mu x * mu z * (∏ i, G i x z)| := le_abs_self _
      _ = |mu x * mu z| * |∏ i, G i x z| := abs_mul _ _
      _ ≤ p ^ 2 * (|G 0 x z| * |G ((0 : Fin (n+1)).succ) x z| * delta ^ n) :=
        mul_le_mul (hpair x z) (product_tail_bound n (fun i => G i x z) delta hd
          (fun i => hentry i x z)) (abs_nonneg _) (sq_nonneg p)
      _ = _ := by ring
  have htwo := two_factor_moment (G 0) (G ((0 : Fin (n+1)).succ)) tau
    (hmoment 0) (hmoment ((0 : Fin (n+1)).succ))
  calc
    _ ≤ ∑ x, ∑ z, (p ^ 2 * delta ^ n) *
        (|G 0 x z| * |G ((0 : Fin (n+1)).succ) x z|) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ => hpoint x z))
    _ = (p ^ 2 * delta ^ n) *
        (∑ x, ∑ z, |G 0 x z| * |G ((0 : Fin (n+1)).succ) x z|) := by
      simp only [Finset.mul_sum]
    _ ≤ (p ^ 2 * delta ^ n) * tau ^ 2 :=
      mul_le_mul_of_nonneg_left htwo (mul_nonneg (sq_nonneg p) (pow_nonneg hd n))
    _ = _ := by ring

end Scalar

section Matrices
variable {I X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]

/-- Each output coordinate uses the same original source label `x`. -/
def commonResponse (T : I → Y → X → ℝ) (mu : X → ℝ) (y : I → Y) : ℝ :=
  ∑ x, (∏ i, T i (y i) x) * mu x

theorem commonResponse_energy (T : I → Y → X → ℝ) (mu : X → ℝ) :
    (∑ y, commonResponse T mu y ^ 2) =
      ∑ x, ∑ z, mu x * mu z * ∏ i, gram (T i) x z := by
  have hg (x z : X) :
      gram (fun (y : I → Y) x => ∏ i, T i (y i) x) x z = ∏ i, gram (T i) x z := by
    unfold gram
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i y => T i y x * T i y z)).symm
  have h := gram_quadratic (fun (y : I → Y) x => ∏ i, T i (y i) x) mu
  simpa only [commonResponse, hg] using h

/-- Genuine real-matrix capped common-source bound. The uniform entry bound
comes from the frozen Gram Cauchy--Schwarz theorem and the diagonal caps. -/
theorem capped_response_energy (n : ℕ) (T : Fin (n+2) → Y → X → ℝ)
    (mu : X → ℝ) (p tau delta : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hdiag : ∀ i x, gram (T i) x x ≤ delta)
    (hmoment : ∀ i, (∑ x, ∑ z, gram (T i) x z ^ 2) ≤ tau ^ 2) :
    (∑ y, commonResponse T mu y ^ 2) ≤ p ^ 2 * tau ^ 2 * delta ^ n := by
  rw [commonResponse_energy]
  exact weighted_product_bound n (fun i x z => gram (T i) x z) mu p tau delta hp hd hmu
    (fun i x z => gram_entry_bound (T i) delta hd (hdiag i) x z) hmoment

end Matrices

section TensorResponse
variable {V X : Type*} [Fintype V] [Fintype X]

/-- Exact tensor-response wrapper for arbitrary dependent coordinate maps.
The moment is measured on the actual common source pairs after those maps. -/
theorem tensorResponse_capped_of_coords (n : ℕ) (T : Fin (n+2) → V → V → ℝ)
    (coords : X → Fin (n+2) → V) (mu : X → ℝ) (p tau delta : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta) (hmu : ∀ x, |mu x| ≤ p)
    (hdiag : ∀ i x, gram (T i) (coords x i) (coords x i) ≤ delta)
    (hmoment : ∀ i,
      (∑ x, ∑ z, gram (T i) (coords x i) (coords z i) ^ 2) ≤ tau ^ 2) :
    (∑ y, AESConcrete.WordColumnGram.tensorResponse T coords mu y ^ 2) ≤
      p ^ 2 * tau ^ 2 * delta ^ n := by
  rw [AESConcrete.WordColumnGram.tensorResponse_energy]
  have hentry (i : Fin (n+2)) (x z : X) :
      |gram (T i) (coords x i) (coords z i)| ≤ delta := by
    have hcs := gram_cauchy (T i) (coords x i) (coords z i)
    apply (sq_le_sq₀ (abs_nonneg _) hd).mp
    rw [sq_abs]
    calc
      _ ≤ gram (T i) (coords x i) (coords x i) *
          gram (T i) (coords z i) (coords z i) := hcs
      _ ≤ delta*delta := mul_le_mul (hdiag i x) (hdiag i z)
        (gram_diagonal_nonneg (T i) (coords z i)) hd
      _ = delta ^ 2 := by ring
  exact weighted_product_bound n (fun i x z => gram (T i) (coords x i) (coords z i))
    mu p tau delta hp hd hmu hentry hmoment

/-- Source-coordinate bijections preserve the whole second Gram moment,
without any pointwise Gram-invariance premise. -/
theorem gram_moment_relabel (T : V → V → ℝ) (e : Equiv.Perm V) :
    (∑ x, ∑ z, gram T (e x) (e z) ^ 2) = ∑ x, ∑ z, gram T x z ^ 2 := by
  have hin (x : V) : (∑ z, gram T (e x) (e z) ^ 2) = ∑ z, gram T (e x) z ^ 2 :=
    Equiv.sum_comp e (fun z => gram T (e x) z ^ 2)
  simp_rw [hin]
  exact Equiv.sum_comp e (fun x => ∑ z, gram T x z ^ 2)

/-- The paper's relabeled common-source interface, directly on the frozen
tensor response. Different coordinates may use different bijections. -/
theorem tensorResponse_capped (n : ℕ) (T : Fin (n+2) → V → V → ℝ)
    (e : Fin (n+2) → Equiv.Perm V) (mu : V → ℝ) (p tau delta : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta) (hmu : ∀ x, |mu x| ≤ p)
    (hdiag : ∀ i x, gram (T i) x x ≤ delta)
    (hmoment : ∀ i, (∑ x, ∑ z, gram (T i) x z ^ 2) ≤ tau ^ 2) :
    (∑ y, AESConcrete.WordColumnGram.tensorResponse T (fun x i => e i x) mu y ^ 2) ≤
      p ^ 2 * tau ^ 2 * delta ^ n := by
  exact tensorResponse_capped_of_coords n T (fun x i => e i x) mu p tau delta hp hd hmu
    (fun i x => hdiag i (e i x))
    (fun i => (gram_moment_relabel (T i) (e i)).trans_le (hmoment i))

end TensorResponse
end AESPaper.CappedSourceGram
