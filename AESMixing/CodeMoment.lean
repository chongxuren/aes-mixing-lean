import AESMixing.Gram
import Mathlib.Logic.Equiv.Prod

/-! A two-projection proof of the low-dimensional real code-moment bound.
The two bijections represent disjoint information sets of an MDS code.
No probabilistic independence between the two projections is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {C V I J : Type*} [Fintype C] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq I]

def pairProjection (e : C ≃ (I → V)) : (C × C) ≃ (I → V × V) :=
  (Equiv.prodCongr e e).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => V) (fun _ => V)).symm

theorem projection_square_sum (e : C ≃ (I → V)) (g : V → V → ℝ) :
    (∑ cd : C × C, (∏ i, g (e cd.1 i) (e cd.2 i)) ^ 2) =
      (∑ ab : V × V, g ab.1 ab.2 ^ 2) ^ Fintype.card I := by
  calc
    (∑ cd : C × C, (∏ i, g (e cd.1 i) (e cd.2 i)) ^ 2) =
        ∑ ab : I → V × V, (∏ i, g (ab i).1 (ab i).2) ^ 2 :=
      Equiv.sum_comp (pairProjection e) (fun ab => (∏ i, g (ab i).1 (ab i).2) ^ 2)
    _ = ∏ _ : I, ∑ ab : V × V, g ab.1 ab.2 ^ 2 :=
      product_column_energy (fun (_ : I) (ab : V × V) => g ab.1 ab.2)
    _ = (∑ ab : V × V, g ab.1 ab.2 ^ 2) ^ Fintype.card I := by simp

/-- Both factors have the same total squared mass after a bijective projection. -/
theorem two_projection_cauchy (e f : C ≃ (I → V)) (g : V → V → ℝ) :
    (∑ cd : C × C,
      |(∏ i, g (e cd.1 i) (e cd.2 i)) * (∏ i, g (f cd.1 i) (f cd.2 i))|) ≤
      (∑ ab : V × V, g ab.1 ab.2 ^ 2) ^ Fintype.card I := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun cd : C × C => |∏ i, g (e cd.1 i) (e cd.2 i)|)
    (fun cd : C × C => |∏ i, g (f cd.1 i) (f cd.2 i)|)
  simp_rw [sq_abs, ← abs_mul] at h
  rw [projection_square_sum e g, projection_square_sum f g] at h
  apply (sq_le_sq₀
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (pow_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _)).mp
  simpa only [pow_two] using h

/-- Unnormalized Gram expansion for two information sets and remaining
coordinates. The normalization of a unit code indicator divides by |C|. -/
theorem low_dimension_code_moment (e f : C ≃ (I → V))
    (rest : C → J → V) (g : V → V → ℝ) (delta : ℝ)
    (hd : 0 ≤ delta) (hg : ∀ x y, |g x y| ≤ delta) :
    |∑ cd : C × C,
      (∏ i, g (e cd.1 i) (e cd.2 i)) *
      (∏ i, g (f cd.1 i) (f cd.2 i)) *
      (∏ j, g (rest cd.1 j) (rest cd.2 j))| ≤
      (∑ ab : V × V, g ab.1 ab.2 ^ 2) ^ Fintype.card I *
        delta ^ Fintype.card J := by
  have hr (cd : C × C) : |∏ j, g (rest cd.1 j) (rest cd.2 j)| ≤
      delta ^ Fintype.card J := by
    rw [Finset.abs_prod]
    calc
      (∏ j, |g (rest cd.1 j) (rest cd.2 j)|) ≤ ∏ _ : J, delta :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hg _ _)
      _ = delta ^ Fintype.card J := by simp
  calc
    _ ≤ ∑ cd : C × C,
        |(∏ i, g (e cd.1 i) (e cd.2 i)) *
         (∏ i, g (f cd.1 i) (f cd.2 i)) *
         (∏ j, g (rest cd.1 j) (rest cd.2 j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ cd : C × C,
        |(∏ i, g (e cd.1 i) (e cd.2 i)) *
         (∏ i, g (f cd.1 i) (f cd.2 i))| * delta ^ Fintype.card J := by
      apply Finset.sum_le_sum
      intro cd _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr cd) (abs_nonneg _)
    _ = (∑ cd : C × C,
        |(∏ i, g (e cd.1 i) (e cd.2 i)) *
         (∏ i, g (f cd.1 i) (f cd.2 i))|) * delta ^ Fintype.card J := by
      rw [Finset.sum_mul]
    _ ≤ (∑ ab : V × V, g ab.1 ab.2 ^ 2) ^ Fintype.card I *
        delta ^ Fintype.card J :=
      mul_le_mul_of_nonneg_right (two_projection_cauchy e f g) (pow_nonneg hd _)

end AESMixing
