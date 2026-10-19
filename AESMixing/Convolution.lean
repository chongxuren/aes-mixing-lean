import AESMixing.Block
import AESMixing.Difference

/-! Finite averaging and convolution estimates used by the source-law proof. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem mixture_energy (w : ι → ℝ) (f : ι → κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    (∑ y, (∑ i, w i * f i y) ^ 2) ≤ ∑ i, w i * ∑ y, f i y ^ 2 := by
  have hl (y : κ) : (∑ i, w i * f i y) ^ 2 ≤ ∑ i, w i * f i y ^ 2 := by
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => w i * f i y) (f := w) (g := fun i => w i * f i y ^ 2)
      (fun i _ => hw i)
      (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      (fun i _ => by nlinarith)
    simpa [hs] using hc
  calc
    (∑ y, (∑ i, w i * f i y) ^ 2) ≤ ∑ y, ∑ i, w i * f i y ^ 2 :=
      Finset.sum_le_sum (fun y _ => hl y)
    _ = ∑ i, w i * ∑ y, f i y ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]

variable {V : Type*} [Fintype V] [AddCommGroup V]

def convolution (p q : V → ℝ) (y : V) : ℝ := ∑ x, p x * q (y - x)

theorem convolution_collision_le (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    (∑ y, convolution p q y ^ 2) ≤ ∑ y, q y ^ 2 := by
  have ht (x : V) : (∑ y, q (y - x) ^ 2) = ∑ y, q y ^ 2 :=
    Equiv.sum_comp (Equiv.subRight x) (fun y => q y ^ 2)
  have h := mixture_energy p (fun x y => q (y - x)) hp hs
  simpa only [convolution, ht, ← Finset.sum_mul, hs, one_mul] using h

theorem convolution_atom_sq_le (p q : V → ℝ) (y : V) :
    convolution p q y ^ 2 ≤ (∑ x, p x ^ 2) * ∑ x, q x ^ 2 := by
  have he : (∑ x, q (y - x) ^ 2) = ∑ x, q x ^ 2 :=
    Equiv.sum_comp (Equiv.subLeft y) (fun x => q x ^ 2)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p (fun x => q (y - x))
  simpa only [convolution, he] using hc

end AESMixing
