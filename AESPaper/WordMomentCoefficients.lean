import AESPaper.WordPhysicalEnergy
import AESPaper.WeightedEncoding

/-!
# Exact physical moment coefficients for the remaining residual cases
-/

set_option autoImplicit false
noncomputable section

namespace AESPaper.WordMomentCoefficients
open AESPaper.WordMarkedMoment (q tau delta)
open AESPaper.WordPhysicalEnergy (momentEnergy momentCoefficient)

theorem q_positive : 0 < q := WordPhysicalEnergy.q_positive

theorem q_nonzero : q ≠ 0 := ne_of_gt q_positive

theorem tau_nonnegative : 0 ≤ tau := by
  exact div_nonneg (by norm_num) q_positive.le

theorem delta_eq_weighted : delta = WeightedEncoding.delta := rfl

theorem delta_nonnegative : 0 ≤ delta := by
  rw [delta_eq_weighted]
  exact WeightedEncoding.delta_nonnegative

theorem sqrt_q : Real.sqrt q = 65536 := by
  rw [q, show (2 : ℝ)^32 = 65536^2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]

/-- Nonnegative coefficients are identified by their exact squares. -/
theorem moment_eq_of_square (ell d : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hs : momentEnergy ell d = c ^ 2) : momentCoefficient ell d = c := by
  apply (sq_eq_sq₀ (WordPhysicalEnergy.momentCoefficient_nonnegative ell d) hc).mp
  rw [WordPhysicalEnergy.momentCoefficient_sq, hs]

theorem moment_4_2 : momentCoefficient 4 2 = tau ^ 2 / q := by
  apply moment_eq_of_square 4 2 _ (div_nonneg (sq_nonneg _) q_positive.le)
  norm_num [momentEnergy] <;> field_simp [q_nonzero] <;> ring

theorem moment_5_2 : momentCoefficient 5 2 = tau ^ 2 * Real.sqrt (delta / q) := by
  apply moment_eq_of_square 5 2 _
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt (div_nonneg delta_nonnegative q_positive.le)]
  norm_num [momentEnergy] <;> field_simp [q_nonzero] <;> ring

theorem moment_5_3 : momentCoefficient 5 3 = tau ^ 2 * Real.sqrt (delta / q) := by
  have he : momentCoefficient 5 3 = momentCoefficient 5 2 := by
    norm_num [momentCoefficient, momentEnergy]
  rw [he, moment_5_2]

theorem moment_6_3 : momentCoefficient 6 3 = tau ^ 3 / 65536 := by
  apply moment_eq_of_square 6 3 _
    (div_nonneg (pow_nonneg tau_nonnegative _) (by norm_num))
  norm_num [momentEnergy, q]
  <;> ring

theorem moment_6_2 : momentCoefficient 6 2 = tau ^ 2 * delta := by
  apply moment_eq_of_square 6 2 _ (mul_nonneg (sq_nonneg _) delta_nonnegative)
  norm_num [momentEnergy] <;> field_simp [q_nonzero] <;> ring

theorem moment_6_4 : momentCoefficient 6 4 = tau ^ 2 * delta := by
  have he : momentCoefficient 6 4 = momentCoefficient 6 2 := by
    norm_num [momentCoefficient, momentEnergy]
  rw [he, moment_6_2]

end AESPaper.WordMomentCoefficients
