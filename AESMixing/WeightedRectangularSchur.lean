import AESMixing.RectangularSchur

/-! A rectangular positive-vector Schur certificate. Both weighted row
and column inequalities are needed; symmetry is not assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem weighted_rectangular_schur_energy {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ℝ) (u : J → ℝ) (v : I → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hA : ∀ y x, 0 ≤ A y x)
    (hu : ∀ y, 0 < u y) (hv : ∀ x, 0 < v x)
    (hrow : ∀ y, (∑ x, A y x * v x) ≤ c*u y)
    (hcol : ∀ x, (∑ y, A y x * u y) ≤ c*v x) (f : I → ℝ) :
    (∑ y, action A f y^2) ≤ c^2 * ∑ x, f x^2 := by
  have hpoint (y : J) : action A f y^2 ≤
      c * ∑ x, A y x * u y / v x * f x^2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun x => A y x*f x)
      (f := fun x => A y x*v x/u y)
      (g := fun x => A y x*u y/v x*f x^2)
      (fun x _ => by have ha := hA y x; have hy := hu y; have hx := hv x; positivity)
      (fun x _ => by have ha := hA y x; have hy := hu y; have hx := hv x; positivity)
      (fun x _ => by
        apply le_of_eq
        have hy := ne_of_gt (hu y)
        have hx := ne_of_gt (hv x)
        field_simp)
    have hm : (∑ x, A y x*v x/u y) ≤ c := by
      rw [← Finset.sum_div]
      exact (div_le_iff₀ (hu y)).mpr (hrow y)
    exact hcs.trans (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg (fun x _ => by
      have ha := hA y x; have hy := hu y; have hx := hv x; positivity)))
  have htotal : (∑ y, ∑ x, A y x*u y/v x*f x^2) ≤ c*∑ x, f x^2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_mul, ← Finset.sum_div]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (hv x)).mpr (hcol x)) (sq_nonneg _)
  calc
    _ ≤ ∑ y, c * ∑ x, A y x*u y/v x*f x^2 := Finset.sum_le_sum (fun y _ => hpoint y)
    _ = c * ∑ y, ∑ x, A y x*u y/v x*f x^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ c*(c*∑ x, f x^2) := mul_le_mul_of_nonneg_left htotal hc
    _ = _ := by ring

end AESMixing
