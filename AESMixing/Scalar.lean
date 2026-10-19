import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
The scalar iteration in Section 7. This module does not assert any AES-specific
contraction or starting estimate. Those are separate formalization obligations.
-/

namespace AESMixing

noncomputable def mixingBound (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ (14 + 61 * k)

theorem mixingBound_pos (k : ℕ) : 0 < mixingBound k := by
  unfold mixingBound
  positivity

theorem mixingBound_zero : mixingBound 0 = 1 / (2 : ℝ) ^ 14 := by
  norm_num [mixingBound]

theorem mixingBound_succ (k : ℕ) :
    mixingBound (k + 1) = mixingBound k * (1 / (2 : ℝ) ^ 61) := by
  simp only [mixingBound, Nat.mul_add, Nat.mul_one, pow_add]
  ring

theorem mixingBound_geometric (k : ℕ) :
    mixingBound k = (1 / (2 : ℝ) ^ 14) * (1 / (2 : ℝ) ^ 61) ^ k := by
  induction k with
  | zero => simp [mixingBound_zero]
  | succ k ih => rw [mixingBound_succ, ih, pow_succ]; ring

theorem geometric_iteration (e : ℕ → ℝ) (a b : ℝ)
    (hb : 0 < b) (initial : e 0 < a)
    (step : ∀ k, e (k + 1) ≤ b * e k) : ∀ k, e k < a * b ^ k := by
  intro k
  induction k with
  | zero => simpa using initial
  | succ k ih =>
      calc
        e (k + 1) ≤ b * e k := step k
        _ < b * (a * b ^ k) := mul_lt_mul_of_pos_left ih hb
        _ = a * b ^ (k + 1) := by rw [pow_succ]; ring

theorem dyadic_square_identity (k : ℕ) :
    ((2 : ℝ) ^ 128 / 4) *
      ((1 / (2 : ℝ) ^ 154) * (1 / (2 : ℝ) ^ 122) ^ k) =
      (mixingBound k) ^ 2 := by
  rw [mixingBound_geometric, mul_pow]
  have hc : ((2 : ℝ) ^ 128 / 4) * (1 / (2 : ℝ) ^ 154) =
      (1 / (2 : ℝ) ^ 14) ^ 2 := by norm_num
  have hp : (1 / (2 : ℝ) ^ 122) ^ k = ((1 / (2 : ℝ) ^ 61) ^ k) ^ 2 := by
    rw [show (1 / (2 : ℝ) ^ 122) = (1 / (2 : ℝ) ^ 61) ^ 2 by norm_num]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
  rw [← mul_assoc, hc, hp]

/-- A conditional scalar induction, not a theorem about the AES cipher. -/
theorem scalar_iteration (e : ℕ → ℝ)
    (initial : e 0 < 1 / (2 : ℝ) ^ 14)
    (step : ∀ k, e (k + 1) ≤ (1 / (2 : ℝ) ^ 61) * e k) :
    ∀ k, e k < mixingBound k := by
  intro k
  induction k with
  | zero => simpa [mixingBound] using initial
  | succ k ih =>
      rw [mixingBound_succ]
      calc
        e (k + 1) ≤ (1 / (2 : ℝ) ^ 61) * e k := step k
        _ < (1 / (2 : ℝ) ^ 61) * mixingBound k :=
          mul_lt_mul_of_pos_left ih (by positivity)
        _ = mixingBound k * (1 / (2 : ℝ) ^ 61) := mul_comm _ _

theorem target_128 : mixingBound 2 < 1 / (2 : ℝ) ^ 128 := by
  norm_num [mixingBound]

theorem target_192 : mixingBound 3 < 1 / (2 : ℝ) ^ 192 := by
  norm_num [mixingBound]

theorem target_256 : mixingBound 4 < 1 / (2 : ℝ) ^ 256 := by
  change 1 / (2 : ℝ) ^ (256 + 2) < 1 / (2 : ℝ) ^ 256
  rw [pow_add]
  norm_num

end AESMixing
