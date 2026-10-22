import AES8.Math.PaperActivityInputArithmetic

/-! The printed sharp frame constant and its scalar substitutions/roundings.
This leaf makes no assertion about an AES operator or response. -/
noncomputable section
namespace AES8.PaperActivityInputSharpArithmetic
open AESMixing WordActivityFrame PaperActivityInputArithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000

def C : ℝ := (1 - xi AES.Word)⁻¹

theorem C_exact : C = (65536 / 65535 : ℝ) := by
  norm_num [C, word_xi]
theorem C_nonneg : 0 ≤ C := by rw [C_exact]; norm_num
theorem C_lt_printed : C < (1000016 / 1000000 : ℝ) := by rw [C_exact]; norm_num
theorem C_six_lt_printed : C^6 < (10001 / 10000 : ℝ) := by rw [C_exact]; norm_num

theorem two_rounding :
    (6480000 : ℝ) * C^6 / 4294967296 < (389/10000 : ℝ)^2 := by
  rw [C_exact]; norm_num
theorem three_rounding :
    (768000 : ℝ) * C^5 / 4294967296 < (134/10000 : ℝ)^2 := by
  rw [C_exact]; norm_num
theorem four_rounding :
    C^4 * ((12800 : ℝ)/4294967296 + 48600000000/4294967296^2)
      < (1728/1000000 : ℝ)^2 := by
  rw [C_exact]; norm_num

theorem moment_substitution (q : ℝ) (hq : q ≠ 0) :
    q^4 * (72 * C^6 * (300/q)^2 / q^3) = 6480000*C^6/q ∧
    q^4 * (64 * C^5 * (300/q)^2 * (2/(15*q)) / q^2) = 768000*C^5/q ∧
    q^4 * (C^4 * (8*(300/q)^2*(2/(15*q))^2/q + 6*(300/q)^4/q^2)) =
      C^4 * (12800/q+48600000000/q^2) := by
  constructor
  · field_simp [hq]; ring
  constructor <;> field_simp [hq] <;> ring

end AES8.PaperActivityInputSharpArithmetic
