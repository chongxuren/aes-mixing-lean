import AESMixing.L2Sums
import AESMixing.ProductProjection

/-!
# Uniform bounds on a matrix of orthogonal blocks

The square-root multiplicity in the paper's exact-support lifting follows
from the actual two orthogonal families and per-block norm caps. No grouped
norm bound is a premise. Empty index families are included.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperOrthogonalBlockLift
open AESMixing
set_option autoImplicit false

variable {I J X Y : Type*} [Fintype I] [Fintype J] [Fintype X] [Fintype Y]

theorem squared_sum_le (a : J → ℝ) :
    (∑ j, a j) ^ 2 ≤ (Fintype.card J : ℝ) * ∑ j, a j ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : J => (1 : ℝ)) a

/-- Cauchy--Schwarz is applied only to the input block lengths. -/
theorem row_energy_le (v : J → X → ℝ) (w : J → Y → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ j, l2 (w j) ≤ c * l2 (v j)) :
    (∑ y, (∑ j, w j y) ^ 2) ≤
      c ^ 2 * (Fintype.card J : ℝ) * ∑ j, l2 (v j) ^ 2 := by
  classical
  have hrow : l2 (fun y => ∑ j, w j y) ≤ c * ∑ j, l2 (v j) := by
    calc
      _ ≤ ∑ j, l2 (w j) := l2_finset_sum_le Finset.univ w
      _ ≤ ∑ j, c * l2 (v j) := Finset.sum_le_sum (fun j _ => h j)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsq := (sq_le_sq₀ (l2_nonneg _) (mul_nonneg hc
    (Finset.sum_nonneg (fun j _ => l2_nonneg (v j))))).mpr hrow
  rw [l2_sq, mul_pow] at hsq
  calc
    _ ≤ c ^ 2 * (∑ j, l2 (v j)) ^ 2 := hsq
    _ ≤ c ^ 2 * ((Fintype.card J : ℝ) * ∑ j, l2 (v j) ^ 2) :=
      mul_le_mul_of_nonneg_left (squared_sum_le (fun j => l2 (v j))) (sq_nonneg c)
    _ = _ := by ring

/-- Literal block matrix action, with both orthogonal decompositions retained. -/
theorem energy_le (v : J → X → ℝ) (w : I → J → Y → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ i j, l2 (w i j) ≤ c * l2 (v j))
    (hin : ∀ j k, j ≠ k → (∑ x, v j x * v k x) = 0)
    (hout : ∀ i k, i ≠ k →
      (∑ y, (∑ j, w i j y) * (∑ j, w k j y)) = 0) :
    (∑ y, (∑ i, ∑ j, w i j y) ^ 2) ≤
      c ^ 2 * ((Fintype.card I : ℝ) * Fintype.card J) *
        ∑ x, (∑ j, v j x) ^ 2 := by
  rw [orthogonal_family_energy _ hout, orthogonal_family_energy _ hin]
  calc
    _ ≤ ∑ _i : I, c ^ 2 * (Fintype.card J : ℝ) * ∑ j, l2 (v j) ^ 2 :=
      Finset.sum_le_sum (fun i _ => row_energy_le v (w i) c hc (h i))
    _ = _ := by
      simp only [l2_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The exact square-root product of the two block counts, including zero. -/
theorem norm_le (v : J → X → ℝ) (w : I → J → Y → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ i j, l2 (w i j) ≤ c * l2 (v j))
    (hin : ∀ j k, j ≠ k → (∑ x, v j x * v k x) = 0)
    (hout : ∀ i k, i ≠ k →
      (∑ y, (∑ j, w i j y) * (∑ j, w k j y)) = 0) :
    l2 (fun y => ∑ i, ∑ j, w i j y) ≤
      c * Real.sqrt ((Fintype.card I : ℝ) * Fintype.card J) *
        l2 (fun x => ∑ j, v j x) := by
  apply l2_le_of_energy _ _ _ (mul_nonneg hc (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact energy_le v w c hc h hin hout

end AES8.PaperOrthogonalBlockLift
