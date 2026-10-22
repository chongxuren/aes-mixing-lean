import AES8.Math.PaperActivityInputGram
import AESConcrete.WordFourierCore
import AESConcrete.WordCrossZero
import AESConcrete.WordColumnBounds

/-! Fixed rational rounding for the activity-input endpoint. The universal
loss L^2 is weaker than the paper's C^(8-i), but suffices for its stated b_i.
This leaf proves arithmetic only; it supplies no physical-operator premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputArithmetic
open AESMixing WordActivityFrame PaperActivityInputGram
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

def loss : ℝ := 10000 / 9999

theorem word_xi : xi AES.Word = 1 / 65536 := by
  unfold xi q
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem word_lower (n : ℕ) (hn : n ≤ 6) :
    (9999 / 10000 : ℝ) ≤ 2-(1+xi AES.Word)^n := by
  rw [word_xi]
  have hp : (1+1/65536 : ℝ)^n ≤ (1+1/65536 : ℝ)^6 :=
    pow_le_pow_right₀ (by norm_num) hn
  norm_num at hp ⊢
  linarith

theorem word_frame_coefficients {N : Type*} [Fintype N] [DecidableEq N]
    (hn : Fintype.card N ≤ 6) (c : (N → Bool) → ℝ) :
    (∑ s, c s ^ 2) ≤ loss *
      ∑ x : N → AES.Word, (∑ s, frameColumn 0 s x * c s)^2 := by
  have h := frame_energy_lower (0 : AES.Word) AESConcrete.AES.word_card_gt_one c
  have h' := mul_le_mul_of_nonneg_right (word_lower (Fintype.card N) hn)
    (show 0 ≤ ∑ s, c s ^ 2 by positivity)
  unfold loss
  nlinarith

theorem two_rounding :
    (6480000 : ℝ) * loss^2 / 4294967296 < (389/10000 : ℝ)^2 := by
  norm_num [loss]
theorem three_rounding :
    (768000 : ℝ) * loss^2 / 4294967296 < (134/10000 : ℝ)^2 := by
  norm_num [loss]
theorem four_rounding :
    loss^2 * ((12800 : ℝ)/4294967296 + 48600000000/4294967296^2)
      < (1728/1000000 : ℝ)^2 := by
  norm_num [loss]

/-- Scalar substitution, with q^4 restored exactly. -/
theorem moment_substitution (q : ℝ) (hq : q ≠ 0) :
    q^4 * (72 * loss^2 * (300/q)^2 / q^3) = 6480000*loss^2/q ∧
    q^4 * (64 * loss^2 * (300/q)^2 * (2/(15*q)) / q^2) = 768000*loss^2/q ∧
    q^4 * (loss^2 * (8*(300/q)^2*(2/(15*q))^2/q + 6*(300/q)^4/q^2)) =
      loss^2 * (12800/q+48600000000/q^2) := by
  constructor
  · field_simp [hq]; ring
  constructor <;> field_simp [hq] <;> ring

end AES8.PaperActivityInputArithmetic
