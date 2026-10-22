import AES8.Recurrence.PaperNormalizedOutput
import AES8.Recurrence.PaperParityInduction

/-!
# Exact current mixing consequence, with remaining profile membership explicit

This implication checks the paper's last deduction on the actual retained-key
AES experiment and current output functional. The concrete alternating boxes
remain a premise. It is not an unconditional proof of the complete AES theorem.
-/

noncomputable section
namespace AES8.PaperCurrentBound
open AESMixing AESMixing.AES PaperOutputEnvelopes

/-- The paper's exact bound, with a natural exponent. -/
def bound (k : ℕ) : ℝ := 7 / 2 ^ (95 + 41 * k)

theorem bound_pos (k : ℕ) : 0 < bound k := by unfold bound; positivity

/-- Actual profile membership, separated from the final distance conclusion. -/
def ActualBoxes : Prop := ∀ a : AES.State, a ≠ 0 → ∀ j : ℕ, 2 ≤ j →
  NormalizedProfile.actual a j ≤ scale 1000 evenEnvelope ∨
  NormalizedProfile.actual a j ≤ scale 1000 oddEnvelope

theorem output_lt (hb : ActualBoxes) (a : AES.State) (ha : a ≠ 0)
    (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) < 112 :=
  PaperOutputEnvelopes.output_lt_of_box _ (NormalizedProfile.actual_nonneg a j) (hb a ha j hj)

theorem coefficient (k : ℕ) :
    (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) * 112 = bound k := by
  unfold omega41 bound
  rw [div_pow, one_pow, ← pow_mul]
  have he : 41 * (k + 2) = 41 * k + 82 := by omega
  rw [he, pow_add, pow_add]
  field_simp
  ring

theorem difference_eight_plus_two (hb : ActualBoxes) (k : ℕ)
    (a : AES.State) (ha : a ≠ 0) :
    tv (physicalDifferenceLaw (8 + 2 * k) a) (uniformExcept (0 : AES.State)) < bound k := by
  have h := PaperNormalizedOutput.actual_output a ha (k + 2)
  have hp : (0 : ℝ) < (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) := by
    exact mul_pos (by positivity) (pow_pos omega41_pos _)
  have hs := mul_lt_mul_of_pos_left (output_lt hb a ha (k + 2) (by omega)) hp
  rw [coefficient] at hs
  have hi : 4 + 2 * (k + 2) = 8 + 2 * k := by omega
  rw [hi] at h
  exact h.trans_lt hs

/-- Exact current theorem, conditional only on the displayed actual-profile
boxes. Their AES recurrence and finite-map derivation remain downstream. -/
theorem epsilon_eight_plus_two (hb : ActualBoxes) (k : ℕ) :
    AES.epsilon (8 + 2 * k) < bound k :=
  epsilon_lt_of_difference_bound (8 + 2 * k) (bound k) (bound_pos k)
    (fun a ha => difference_eight_plus_two hb k a ha)

/-- The current constant is strictly below the historical dyadic endpoint. -/
theorem bound_lt_dyadic (k : ℕ) : bound k < ConcreteBridge.dyadicBound k := by
  unfold bound ConcreteBridge.dyadicBound
  rw [show 95 + 41 * k = (92 + 41 * k) + 3 by omega, pow_add]
  have hp : (0 : ℝ) < 2 ^ (92 + 41 * k) := by positivity
  apply (div_lt_div_iff₀ (mul_pos hp (by positivity)) hp).mpr
  norm_num
  linarith

theorem ten_round_exact (hb : ActualBoxes) : AES.epsilon 10 < (1 : ℝ) / 2 ^ (133 : ℕ) :=
  (epsilon_eight_plus_two hb 1).trans (by norm_num [bound])

theorem ten_round_128 (hb : ActualBoxes) : AES.epsilon 10 < (1 : ℝ) / 2 ^ (128 : ℕ) :=
  (ten_round_exact hb).trans (by norm_num)

theorem fourteen_round_exact (hb : ActualBoxes) : AES.epsilon 14 < (1 : ℝ) / 2 ^ (215 : ℕ) :=
  (epsilon_eight_plus_two hb 3).trans (by norm_num [bound])

theorem fourteen_round_192 (hb : ActualBoxes) : AES.epsilon 14 < (1 : ℝ) / 2 ^ (192 : ℕ) :=
  (fourteen_round_exact hb).trans (by norm_num)

theorem sixteen_round_256 (hb : ActualBoxes) : AES.epsilon 16 < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  (epsilon_eight_plus_two hb 4).trans (by
    simpa only [ConcreteBridge.dyadicBound] using bound_lt_dyadic 4)

end AES8.PaperCurrentBound
