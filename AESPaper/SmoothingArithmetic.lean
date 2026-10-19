import AESPaper.Arithmetic

/-!
Rational consequences used by the one-source case in v9 Appendix D.5.
The source-law and orthogonal-decomposition estimates are not assumed proved
by these numerical checks. q=2^32 throughout.
-/
set_option autoImplicit false
namespace AESPaper.SmoothingArithmetic
noncomputable section
def q : ℝ := 2^32
def ratio : ℝ := q / (q-1)

theorem reference_activity :
    q^5 * (1 / (q-1)^4 - 1 / (q^4-1)) < (4001/1000 : ℝ) := by
  norm_num [q]

theorem activity_profile : (4001/1000 : ℝ) < (21/10)^2 := by norm_num

theorem degree_one : 4 * (49/5) * ratio^3 < (63/10 : ℝ)^2 := by
  norm_num [ratio, q]

theorem degree_two : 6 * ratio^2 * 36000000 / q < (1/4 : ℝ)^2 := by
  norm_num [ratio, q]

theorem degree_three : 4 * ratio * (2/15) * 36000000 / q < (7/100 : ℝ)^2 := by
  norm_num [ratio, q]

theorem degree_four : (2/15)^2 * 36000000 / q < (1/80 : ℝ)^2 := by
  norm_num [q]

end
end AESPaper.SmoothingArithmetic
