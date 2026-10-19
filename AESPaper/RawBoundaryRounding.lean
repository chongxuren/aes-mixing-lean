import AESPaper.ResidualRounding
import AESPaper.ReverseResidualChoices

/-!
# Exact scalar rounding for the unscaled raw boundary table
-/

set_option autoImplicit false
noncomputable section

namespace AESPaper.RawBoundaryRounding
open AESPaper.Assembly (q)
open AESPaper.ResidualRounding (coefficient coefficient_le_of_sq)

def raw11 : ℝ := 3 / (q * 65536)
def raw12 : ℝ := HardActivityArrays.coefficient32 / q
def raw13 : ℝ := Real.sqrt 13 / 65536
def raw22 : ℝ := HardActivityArrays.lambda22 (1 / 65536) (1 / q)
def raw2 : ℝ := Real.sqrt 12 / q
def raw3 : ℝ := 4 / 65536

theorem raw11_nonnegative : 0 ≤ raw11 := by norm_num [raw11, q]
theorem raw12_nonnegative : 0 ≤ raw12 :=
  div_nonneg HardActivityArrays.coefficient32_positive.le (by norm_num [q])
theorem raw13_nonnegative : 0 ≤ raw13 := by unfold raw13; positivity
theorem raw22_nonnegative : 0 ≤ raw22 :=
  HardActivityArrays.lambda22_nonnegative _ _ (by norm_num [q])
theorem raw2_nonnegative : 0 ≤ raw2 := by unfold raw2 q; positivity
theorem raw3_nonnegative : 0 ≤ raw3 := by norm_num [raw3]

theorem sqrt13_upper : Real.sqrt (13 : ℝ) ≤ 90139 / 25000 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 90139/25000)).mp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 13)]
  norm_num

theorem raw22_upper : raw22 ≤ 200003 / (100000 * 65536) := by
  have hs : Real.sqrt ((1 / q : ℝ)^2 + 16 * (1/65536:ℝ)^2) ≤
      400000001 / (100000000 * 65536) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (by norm_num : (0:ℝ) ≤ 400000001 / (100000000 * 65536))).mp
    rw [Real.sq_sqrt (by positivity)]
    norm_num [q]
  unfold raw22 HardActivityArrays.lambda22
  norm_num [q] at hs ⊢
  linarith

theorem round11 : coefficient 1 1 raw11 ≤ Assembly.C 0 0 := by
  apply coefficient_le_of_sq 1 1 raw11 _ raw11_nonnegative
    (by norm_num [Assembly.C, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [raw11, q, Nat.choose, Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round12 : coefficient 1 2 raw12 ≤ Assembly.C 0 1 := by
  apply coefficient_le_of_sq 1 2 raw12 _ raw12_nonnegative
    (by norm_num [Assembly.C, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  simp only [raw12, div_pow, HardActivityArrays.coefficient32_sq,
    HardActivityArrays.rho32]
  have hs := sqrt13_upper
  norm_num [q, Nat.choose, Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at *
  linarith

theorem round13 : coefficient 1 3 raw13 ≤ Assembly.C 0 2 := by
  apply coefficient_le_of_sq 1 3 raw13 _ raw13_nonnegative
    (by norm_num [Assembly.C, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  simp only [raw13, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 13)]
  norm_num [q, Nat.choose, Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round22 : coefficient 2 2 raw22 ≤ Assembly.C 1 1 := by
  apply (ResidualRounding.coefficient_mono 2 2 raw22_upper).trans
  apply coefficient_le_of_sq 2 2 _ _ (by norm_num)
    (by norm_num [Assembly.C, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [q, Nat.choose, Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round20 : coefficient 2 0 raw2 ≤ Assembly.t 1 := by
  apply coefficient_le_of_sq 2 0 raw2 _ raw2_nonnegative
    (by norm_num [Assembly.t, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  simp only [raw2, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)]
  norm_num [q, Nat.choose, Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem round30 : coefficient 3 0 raw3 ≤ Assembly.t 2 := by
  apply coefficient_le_of_sq 3 0 raw3 _ raw3_nonnegative
    (by norm_num [Assembly.t, q, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail])
  norm_num [raw3, q, Nat.choose, Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

end AESPaper.RawBoundaryRounding
