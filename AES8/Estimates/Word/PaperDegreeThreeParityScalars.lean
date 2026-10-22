import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Scalar comparisons in the frozen paper's degree-three parity argument

These are precisely the metric and final Schur-complement scalar margins
in `12-word-resources.tex` at f902bb94. They do not assert the underlying
parity-operator, tensor-spectrum, response-row or cross-parity norm bounds.
Those are separate correspondence obligations in this branch's record.
-/

namespace AES8.PaperDegreeThreeParityScalars

theorem tensor_lower : (127 / 128 : ℝ) < (1 - (1 / 16 : ℝ)^2)^2 := by norm_num

theorem odd_correction :
    (4 * (1 / 16 : ℝ)^2 * (1 + (1 / 16 : ℝ)^2)^2 /
      (1 - (1 / 16 : ℝ)^4)) = (1 / 64 : ℝ) * (257 / 255) ∧
    (1 / 64 : ℝ) * (257 / 255) < 3 / 128 := by norm_num

theorem even_correction :
    (12 * (1 / 16 : ℝ)^4 / (1 - (1 / 16 : ℝ)^4)) = (12 / 65535 : ℝ) ∧
    (12 / 65535 : ℝ) < 1 / 128 := by norm_num

theorem odd_metric_margin : (127 / 128 - 3 / 128 : ℝ) = 31 / 32 := by norm_num
theorem even_metric_margin : (127 / 128 - 1 / 128 : ℝ) = 63 / 64 := by norm_num

theorem gram_scale : (1024 / 255 : ℝ) < 201 / 50 := by norm_num

theorem odd_slack :
    ((33 / 10 : ℝ)^2 * (31 / 32) - (201 / 50) * (9 / 8)) = 19287 / 3200 ∧
    (6 : ℝ) < 19287 / 3200 := by norm_num

theorem even_slack :
    ((33 / 10 : ℝ)^2 * (63 / 64) - (201 / 50) * (229 / 100)) = 242247 / 160000 ∧
    (3 / 2 : ℝ) < 242247 / 160000 := by norm_num

theorem cross_parity :
    (71091009 / 104857600 + 23122 / 159375 : ℝ) < 17 / 25 + 3 / 20 ∧
    (17 / 25 + 3 / 20 : ℝ) = 83 / 100 ∧
    (83 / 100 : ℝ) < 5 / 6 := by norm_num

theorem cross_row_column_product : (5 / 2 * (10 / 3) : ℝ) = 25 / 3 := by norm_num
theorem final_schur_margin : (3 / 2 - ((25 / 3) / 6) : ℝ) = 1 / 9 := by norm_num

end AES8.PaperDegreeThreeParityScalars
