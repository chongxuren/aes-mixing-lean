import AESMixing.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

/-! Quadratic estimates on finite real vectors, with counting measure. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι : Type*} [Fintype ι]

/-- The positive-vector certificate used for the local symmetric comparison. -/
theorem weighted_schur_energy (A : ι → ι → ℝ) (v : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hA : ∀ i j, 0 ≤ A i j)
    (hsym : ∀ i j, A i j = A j i) (hv : ∀ i, 0 < v i)
    (hrow : ∀ i, ∑ j, A i j * v j ≤ c * v i) (x : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) ^ 2) ≤ c ^ 2 * ∑ j, x j ^ 2 := by
  have hquot (i : ι) : (∑ j, A i j * v j) / v i ≤ c :=
    (div_le_iff₀ (hv i)).mpr (hrow i)
  have hlocal (i : ι) :
      (∑ j, A i j * x j) ^ 2 ≤ c * ∑ j, A i j * v i / v j * x j ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => A i j * x j)
      (f := fun j => A i j * v j / v i)
      (g := fun j => A i j * v i / v j * x j ^ 2)
      (fun j _ => by have ha := hA i j; have hi := hv i; have hj := hv j; positivity)
      (fun j _ => by have ha := hA i j; have hi := hv i; have hj := hv j; positivity)
      (fun j _ => by
        apply le_of_eq
        have hi := ne_of_gt (hv i)
        have hj := ne_of_gt (hv j)
        field_simp)
    have hsum : (∑ j, A i j * v j / v i) ≤ c := by
      rw [← Finset.sum_div]
      exact hquot i
    exact hcs.trans (mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg (fun j _ => by
        have ha := hA i j; have hi := hv i; have hj := hv j; positivity)))
  have hdouble :
      (∑ i, ∑ j, A i j * v i / v j * x j ^ 2) ≤ c * ∑ j, x j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.sum_mul, ← Finset.sum_div]
    have hs : (∑ i, A i j * v i) = ∑ i, A j i * v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsym i j]
    rw [hs]
    exact mul_le_mul_of_nonneg_right (hquot j) (sq_nonneg (x j))
  calc
    (∑ i, (∑ j, A i j * x j) ^ 2)
        ≤ ∑ i, c * ∑ j, A i j * v i / v j * x j ^ 2 :=
          Finset.sum_le_sum (fun i _ => hlocal i)
    _ = c * ∑ i, ∑ j, A i j * v i / v j * x j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ c * (c * ∑ j, x j ^ 2) := mul_le_mul_of_nonneg_left hdouble hc
    _ = c ^ 2 * ∑ j, x j ^ 2 := by ring

/-- Exact two-by-two comparison from the four-round contraction proof. -/
theorem two_block_energy (a b : ℝ) :
    (7 * a + b / 2) ^ 2 + (a / 2 + 15 * b / 2) ^ 2 ≤
      64 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

end AESMixing
