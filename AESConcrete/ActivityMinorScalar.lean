import AESConcrete.ActivityCodeScalar

/-!
# Exact scalar comparisons for the activity minor route

These coefficients are candidate physical energy envelopes. This file verifies
only their nonnegativity and comparison with the unchanged rational certificate.
The operator inequalities are separate obligations; no pair is added to the
accepted step-cap inventory by a scalar comparison.

Constructive mathematics only; no attacks, manuscript or historical edits.
Independent retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the 10/14/16 target remain unchanged.
-/

noncomputable section
namespace AESConcrete.ActivityMinorScalar
open AESConcrete.ActivityCodeScalar (q s)
open AESConcrete.RefinedStepZeros (blockType)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Squared energy envelope, with the common moment coefficient kept exact. -/
def squaredBound (i : Fin 14) (b : ℕ) : ℝ :=
  if i = 8 then
    6 * (Nat.choose 4 b : ℝ) * (300 / q) ^ 2 * (Nat.choose b 3 : ℝ) ^ 2 /
      (q - 1) ^ b
  else if i = 9 then
    12 * (Nat.choose 4 b : ℝ) * (300 / q) ^ 2 *
      ((Nat.choose b 2 : ℝ) + (Nat.choose b 3 : ℝ)) ^ 2 / (q - 1) ^ (b + 1)
  else if i = 10 then
    6 * (Nat.choose 4 b : ℝ) * (300 / q) ^ 2 *
      ((b : ℝ) + 2 * (Nat.choose b 2 : ℝ) + (Nat.choose b 3 : ℝ)) ^ 2 /
      (q - 1) ^ (b + 2)
  else if i = 11 then
    4 * (Nat.choose 4 b : ℝ) * (12000 / q ^ 5) *
      ((Nat.choose b 2 : ℝ) * q + (Nat.choose b 3 : ℝ) * q * s) ^ 2 /
      (q - 1) ^ b
  else if i = 12 then
    4 * (Nat.choose 4 b : ℝ) * (12000 / q ^ 4) *
      ((b : ℝ) * s + (Nat.choose b 2 : ℝ) * (q + s) +
        (Nat.choose b 3 : ℝ) * q) ^ 2 / (q - 1) ^ (b + 1)
  else 0

theorem squaredBound_nonneg (i : Fin 14) (b : ℕ) : 0 ≤ squaredBound i b := by
  unfold squaredBound q s
  split_ifs <;> positivity

/-- Candidate locations only; membership does not assert an operator bound. -/
def minorPair (i j : Fin 14) : Prop :=
  (i = 8 ∧ (j = 2 ∨ j = 3)) ∨
  (i = 9 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
  (i = 10 ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3)) ∨
  (i = 11 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
  (i = 12 ∧ (j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3))

instance (i j : Fin 14) : Decidable (minorPair i j) := by
  unfold minorPair
  infer_instance

theorem certificate_minor_bounds (i j : Fin 14) (h : minorPair i j) :
    0 ≤ lambda * L i j ∧
      squaredBound i (blockType j).2 ≤ (lambda * L i j) ^ 2 := by
  -- Reduce Fin numerals to constructors before evaluating the vector table.
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | (norm_num [squaredBound, q, s, Nat.choose, blockType, Fin.ext_iff,
        AESRound.Terminal.lambda, AESRound.Certificate.L])

end AESConcrete.ActivityMinorScalar
