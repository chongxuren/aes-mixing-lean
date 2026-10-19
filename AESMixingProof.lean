import AESPaper.Propagation
import AESPaper.FullPermutationOutput

/-!
# AES mixing with independent retained round keys

The concrete cipher, key distribution and pairwise total variation distance are
`AESMixing.AES.encrypt`, `AESMixing.uniformKeyWeight` and `AESMixing.AES.epsilon`.
The cipher includes initial whitening and omits the final MixColumns operation.
The round keys are independent uniform 128-bit states, sampled once and retained.

The public entry points below expose the exact fixed bound and its sufficient
round counts. The stopped two-query output theorem is
`AESPaper.FullPermutationOutput.output_tv_bound`; it allows finite independent
private randomness and prior information, and finite output types.
-/

set_option autoImplicit false

namespace AESMixingProof

/-- Exact rational estimate and exact rational interpretation of 14.3 + 73.1k. -/
theorem pair_mixing (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    AESMixing.AES.epsilon r <
        (1 / ((2 : ℝ) ^ 12 * 5)) * (1 / ((2 : ℝ) ^ 64 * 560)) ^ k ∧
      (1 / ((2 : ℝ) ^ 12 * 5)) * (1 / ((2 : ℝ) ^ 64 * 560)) ^ k <
        (2 : ℝ) ^ (-(143 / 10 : ℝ) - (731 / 10 : ℝ) * k) := by
  simpa only [AESPaper.rationalBound, AESPaper.initialCoefficient,
    AESPaper.blockRate, AESPaper.decimalBound] using
    AESPaper.Propagation.epsilon_bound k r hr

theorem rounds_128 : AESMixing.AES.epsilon 12 < (2 : ℝ) ^ (-128 : ℝ) :=
  AESPaper.Propagation.rounds_128

theorem rounds_192 : AESMixing.AES.epsilon 16 < (2 : ℝ) ^ (-192 : ℝ) :=
  AESPaper.Propagation.rounds_192

theorem rounds_256 : AESMixing.AES.epsilon 20 < (2 : ℝ) ^ (-256 : ℝ) :=
  AESPaper.Propagation.rounds_256

end AESMixingProof
