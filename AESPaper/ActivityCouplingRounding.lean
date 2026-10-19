import AESPaper.ActivityCouplingChoices
import AESPaper.ResidualRounding

/-!
# Exact rounding for the activity couplings
-/

set_option autoImplicit false
noncomputable section

namespace AESPaper.ActivityCouplingRounding
open AESPaper.ActivityCouplingChoices

def raw2 : ℝ := Real.sqrt 12 * e2
def raw3 : ℝ := 4 * e3
def raw4 : ℝ := Real.sqrt (8 * A4 ^ 2 + 6 * B4 ^ 2)

theorem raw2_nonnegative : 0 ≤ raw2 :=
  mul_nonneg (Real.sqrt_nonneg _) e2_nonnegative

theorem raw3_nonnegative : 0 ≤ raw3 := mul_nonneg (by norm_num) e3_nonnegative

theorem raw4_nonnegative : 0 ≤ raw4 := Real.sqrt_nonneg _

theorem raw2_sq : raw2 ^ 2 = 12 * e2 ^ 2 := by
  rw [raw2, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]

theorem raw3_sq : raw3 ^ 2 =
    16 * (WordMarkedMoment.tau ^ 2 * WordMarkedMoment.delta /
      WordMarkedMoment.q ^ 2) := by
  simp only [raw3, e3, mul_pow, div_pow,
    Real.sq_sqrt WordMomentCoefficients.delta_nonnegative]
  ring

theorem raw4_sq : raw4 ^ 2 = 8 * A4 ^ 2 + 6 * B4 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem round20 : ResidualRounding.coefficient 2 0 raw2 ≤
    Assembly.b 1 / Assembly.q ^ 2 := by
  apply ResidualRounding.coefficient_le_of_sq 2 0 raw2 _ raw2_nonnegative
    (by norm_num [Assembly.b, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw2_sq]
  norm_num [e2, WordMarkedMoment.tau, WordMarkedMoment.q, Nat.choose,
    Assembly.b, Assembly.q, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round30 : ResidualRounding.coefficient 3 0 raw3 ≤
    Assembly.b 2 / Assembly.q ^ 2 := by
  apply ResidualRounding.coefficient_le_of_sq 3 0 raw3 _ raw3_nonnegative
    (by norm_num [Assembly.b, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw3_sq]
  norm_num [WordMarkedMoment.tau, WordMarkedMoment.delta,
    WordMarkedMoment.q, Nat.choose, Assembly.b, Assembly.q,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.vecHead, Matrix.vecTail]

theorem round40 : ResidualRounding.coefficient 4 0 raw4 ≤
    Assembly.b 3 / Assembly.q ^ 2 := by
  apply ResidualRounding.coefficient_le_of_sq 4 0 raw4 _ raw4_nonnegative
    (by norm_num [Assembly.b, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  rw [raw4_sq]
  norm_num [A4, B4, WordMarkedMoment.tau, WordMarkedMoment.delta,
    WordMarkedMoment.q, Nat.choose, Assembly.b, Assembly.q,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.vecHead, Matrix.vecTail]

end AESPaper.ActivityCouplingRounding
