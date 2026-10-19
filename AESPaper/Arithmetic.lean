import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Exact numerical end of the v9 AES mixing theorem (Appendix D, startup).
This file proves arithmetic, not the concrete AES experiment bounds.
The decimal exponents are the exact rationals 143/10 and 731/10.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace AESPaper

noncomputable def initialCoefficient : ℝ := 1 / (2 ^ 12 * 5)
noncomputable def blockRate : ℝ := 1 / (2 ^ 64 * 560)
noncomputable def rationalBound (k : ℕ) : ℝ := initialCoefficient * blockRate ^ k
noncomputable def decimalBound (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(143 / 10 : ℝ) - (731 / 10 : ℝ) * k)

theorem initialCoefficient_pos : 0 < initialCoefficient := by
  norm_num [initialCoefficient]

theorem blockRate_pos : 0 < blockRate := by norm_num [blockRate]

theorem integer_rounding_start : (2 : ℕ) ^ 23 < 5 ^ 10 := by norm_num
theorem integer_rounding_rate : (2 : ℕ) ^ 51 < 35 ^ 10 := by norm_num

theorem initial_decimal_rounding : initialCoefficient < (2 : ℝ) ^ (-(143 / 10 : ℝ)) := by
  apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg (by norm_num) _)
  have h : ((2 : ℝ) ^ (-(143 / 10 : ℝ))) ^ (10 : ℕ) = (2 : ℝ) ^ (-143 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h]
  norm_num [initialCoefficient, Real.rpow_neg]

theorem rate_decimal_rounding : blockRate < (2 : ℝ) ^ (-(731 / 10 : ℝ)) := by
  apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg (by norm_num) _)
  have h : ((2 : ℝ) ^ (-(731 / 10 : ℝ))) ^ (10 : ℕ) = (2 : ℝ) ^ (-731 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_ofNat]
  -- Keep each evaluated exponent below Lean's numeral-evaluation threshold.
  rw [show (731 : ℕ) = 100 * 7 + 31 by decide, pow_add, pow_mul]
  norm_num [blockRate]

theorem rational_lt_decimal (k : ℕ) : rationalBound k < decimalBound k := by
  unfold rationalBound decimalBound
  calc
    initialCoefficient * blockRate ^ k <
        (2 : ℝ) ^ (-(143 / 10 : ℝ)) * blockRate ^ k :=
      mul_lt_mul_of_pos_right initial_decimal_rounding (pow_pos blockRate_pos k)
    _ ≤ (2 : ℝ) ^ (-(143 / 10 : ℝ)) * ((2 : ℝ) ^ (-(731 / 10 : ℝ))) ^ k :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_of_lt blockRate_pos) (le_of_lt rate_decimal_rounding) k)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem decimal_rounds_128 : decimalBound 2 < (2 : ℝ) ^ (-128 : ℝ) := by
  unfold decimalBound
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
  norm_num

theorem decimal_rounds_192 : decimalBound 3 < (2 : ℝ) ^ (-192 : ℝ) := by
  unfold decimalBound
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
  norm_num

theorem decimal_rounds_256 : decimalBound 4 < (2 : ℝ) ^ (-256 : ℝ) := by
  unfold decimalBound
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
  norm_num

end AESPaper
