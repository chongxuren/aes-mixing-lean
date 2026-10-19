import AESMixing.WeightedRectangularSchur

/-! Remove the square roots in a support-size comparison by a positive
diagonal scaling. The remaining certificate consists of rational row and
column inequalities, with no matrix spectral theorem assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem diagonal_comparison_energy {I J : Type*} [Fintype I] [Fintype J]
    (R : J → I → ℝ) (d : J → ℝ) (e : I → ℝ)
    (u : J → ℝ) (v : I → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hR : ∀ y x, 0 ≤ R y x)
    (hd : ∀ y, 0 < d y) (he : ∀ x, 0 < e x)
    (hu : ∀ y, 0 < u y) (hv : ∀ x, 0 < v x)
    (hrow : ∀ y, (∑ x, R y x * e x * v x) ≤ c*u y)
    (hcol : ∀ x, (∑ y, R y x * d y * u y) ≤ c*v x) (f : I → ℝ) :
    (∑ y, action (fun y x => Real.sqrt (d y) * R y x * Real.sqrt (e x)) f y^2) ≤
      c^2 * ∑ x, f x^2 := by
  apply weighted_rectangular_schur_energy _ (fun y => Real.sqrt (d y)*u y)
    (fun x => Real.sqrt (e x)*v x) c hc
  · intro y x
    have h := hR y x
    positivity
  · intro y
    exact mul_pos (Real.sqrt_pos.2 (hd y)) (hu y)
  · intro x
    exact mul_pos (Real.sqrt_pos.2 (he x)) (hv x)
  · intro y
    have ht (x : I) : Real.sqrt (d y)*R y x*Real.sqrt (e x)*
        (Real.sqrt (e x)*v x) = Real.sqrt (d y)*(R y x*e x*v x) := by
      calc
        _ = (Real.sqrt (d y)*R y x*v x) * (Real.sqrt (e x)*Real.sqrt (e x)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (le_of_lt (he x))]; ring
    simp_rw [ht]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (hrow y) (Real.sqrt_nonneg (d y))
    nlinarith
  · intro x
    have ht (y : J) : Real.sqrt (d y)*R y x*Real.sqrt (e x)*
        (Real.sqrt (d y)*u y) = Real.sqrt (e x)*(R y x*d y*u y) := by
      calc
        _ = (Real.sqrt (e x)*R y x*u y) * (Real.sqrt (d y)*Real.sqrt (d y)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (le_of_lt (hd y))]; ring
    simp_rw [ht]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (hcol x) (Real.sqrt_nonneg (e x))
    nlinarith

end AESMixing
