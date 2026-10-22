import AES8.Recurrence.PaperTwoStepAlternating
import AES8.Recurrence.PaperOutputEnvelopes

/-!
# From four fixed profile tests to every later index

This is the paper's shifted alternating induction. Its explicit premises are
nonnegative comparison matrices, their two envelope tests, the two starting
tests, and the memory recurrence. Concrete graph-map tests and actual AES
recurrence estimates are separate obligations; none is supplied by this leaf.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperParityInduction
open AESRound PaperOutputEnvelopes

/-- Starting at indices two and three, the two invariant boxes alternate. -/
theorem parity_bounds {B C : Fin 14 → Fin 14 → ℝ}
    (hB : EntrywiseNonnegative B) (hC : EntrywiseNonnegative C)
    {z : ℕ → AES8.Profile}
    (hrec : PaperTwoStep.MemoryRecurrence B C z)
    (htest_even : (fun i => matVec B oddEnvelope i + matVec C evenEnvelope i) ≤ evenEnvelope)
    (htest_odd : (fun i => matVec B evenEnvelope i + matVec C oddEnvelope i) ≤ oddEnvelope)
    (hstart_even : z 2 ≤ AES8.scale 1000 evenEnvelope)
    (hstart_odd : z 3 ≤ AES8.scale 1000 oddEnvelope) :
    ∀ k, (z (2 * k + 2) ≤ AES8.scale 1000 evenEnvelope) ∧
      (z (2 * k + 3) ≤ AES8.scale 1000 oddEnvelope) := by
  have hs : PaperTwoStep.MemoryRecurrence B C (fun j => z (j + 2)) := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec (n + 2)
  have h := PaperTwoStep.alternating_geometric_bound hB hC
    (d0 := evenEnvelope) (d1 := oddEnvelope)
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1000 by norm_num) hs
    (by simpa using htest_even) (by simpa using htest_odd)
    hstart_even (by
      intro i
      have hi := hstart_odd i
      dsimp only [AES8.scale] at hi
      simpa only [mul_one] using hi)
  intro k
  constructor
  · intro i
    simpa only [one_pow, mul_one, AES8.scale] using (h k).1 i
  · intro i
    simpa only [one_pow, mul_one, AES8.scale, Nat.add_assoc] using (h k).2 i

/-- The exact index restriction in the paper is two, corresponding to eight
rounds after the four-round startup and two-round normalization. -/
theorem box_of_parity {z : ℕ → AES8.Profile}
    (h : ∀ k, (z (2 * k + 2) ≤ AES8.scale 1000 evenEnvelope) ∧
      (z (2 * k + 3) ≤ AES8.scale 1000 oddEnvelope)) (j : ℕ) (hj : 2 ≤ j) :
    z j ≤ AES8.scale 1000 evenEnvelope ∨ z j ≤ AES8.scale 1000 oddEnvelope := by
  have hparity : (j - 2) % 2 = 0 ∨ (j - 2) % 2 = 1 := by omega
  rcases hparity with he | ho
  · left
    have heq : 2 * ((j - 2) / 2) + 2 = j := by omega
    simpa only [heq] using (h ((j - 2) / 2)).1
  · right
    have heq : 2 * ((j - 2) / 2) + 3 = j := by omega
    simpa only [heq] using (h ((j - 2) / 2)).2

theorem output_lt_of_parity {z : ℕ → AES8.Profile}
    (hz : ∀ j i, 0 ≤ z j i)
    (h : ∀ k, (z (2 * k + 2) ≤ AES8.scale 1000 evenEnvelope) ∧
      (z (2 * k + 3) ≤ AES8.scale 1000 oddEnvelope)) (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (z j) < 112 :=
  PaperOutputEnvelopes.output_lt_of_box (z j) (hz j) (box_of_parity h j hj)

end AES8.PaperParityInduction
