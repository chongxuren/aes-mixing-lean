/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.Block
import AESPaper.StartingWord

/-! Shared conversion from a squared-energy estimate to a scaled length.
The analytic energy bound and the exact scalar comparison remain separate inputs.
No AES estimate or source assumption is supplied by this conversion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.ScaledEnergy
open AESMixing

variable {I : Type*} [Fintype I]

theorem scaled_l2_le (f : I → ℝ) (scale budget cap : ℝ)
    (hscale : 0 ≤ scale) (hcap : 0 ≤ cap)
    (henergy : (∑ i, f i ^ 2) ≤ budget)
    (hbudget : scale ^ 2 * budget ≤ cap ^ 2) :
    scale * l2 f ≤ cap := by
  apply (sq_le_sq₀ (mul_nonneg hscale (l2_nonneg f)) hcap).mp
  rw [mul_pow, l2_sq]
  exact (mul_le_mul_of_nonneg_left henergy (sq_nonneg scale)).trans hbudget

/-- The normalization shared by the actual first-high moment proofs. -/
theorem two_pow_eighty_sq : ((2 : ℝ) ^ 80) ^ 2 = AESPaper.StartingWord.q ^ 5 := by
  norm_num [AESPaper.StartingWord.q]

theorem aes_scaled_l2_le (f : I → ℝ) (budget cap : ℝ)
    (hcap : 0 ≤ cap) (henergy : (∑ i, f i ^ 2) ≤ budget)
    (hbudget : AESPaper.StartingWord.q ^ 5 * budget ≤ cap ^ 2) :
    (2 : ℝ) ^ 80 * l2 f ≤ cap := by
  apply scaled_l2_le f ((2 : ℝ) ^ 80) budget cap (by positivity) hcap henergy
  simpa only [two_pow_eighty_sq] using hbudget

end AES8.ScaledEnergy
