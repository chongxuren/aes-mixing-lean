import AESConcrete.RefinedStepZeros
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Scalar certificates for activity-only word-code moments

The five term norm caps belong to the normalized subgroup-indicator
expansion. The binomial numerator applies its expansion coefficients once;
the selected-support factor `choose(4,b)` is applied only after squaring.
The odd denominator powers remain exact. Actual subgroup geometry and
moment energy estimates belong to the analytic modules, while operator
conversion and the pair inventory belong to `ActivityCodeStepCaps`.

Constructive mathematics only; no attacks, workloads, historical or
manuscript edits. Independent uniform retained keys, whitening, omitted
final MixColumns, ordered-distinct pairs and the 10/14/16 target stay fixed.
No return, initialization, experiment linkage or complete AES theorem is
asserted. Compilation and independent review precede acceptance.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityCodeScalar
open AESConcrete.RefinedStepZeros (blockType)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

def q : ℝ := 4294967296
def s : ℝ := 65536

theorem q_pos : 0 < q := by norm_num [q]
theorem s_pos : 0 < s := by norm_num [s]
theorem q_sub_one_pos : 0 < q - 1 := by norm_num [q]
theorem s_sq : s ^ 2 = q := by norm_num [s, q]

/-- Norm envelopes for dimensions zero through four; other dimensions
are assigned zero and never used by the four-coordinate analytic proof. -/
def termNorm (t : ℕ) : ℝ :=
  if t = 1 ∨ t = 3 then 40 / (q ^ 2 * s)
  else if t = 2 then 90000 / q ^ 3 else 0

theorem termNorm_nonneg (t : ℕ) : 0 ≤ termNorm t := by
  unfold termNorm q s
  split_ifs <;> positivity

theorem termNorm_zero : termNorm 0 = 0 := by norm_num [termNorm]
theorem termNorm_four : termNorm 4 = 0 := by norm_num [termNorm]

/-- The exact size-grouped norm numerator before its normalization. -/
def numerator (b : ℕ) : ℝ :=
  ∑ t : Fin (b + 1), (Nat.choose b t.val : ℝ) * s ^ t.val * termNorm t.val

theorem numerator_nonneg (b : ℕ) : 0 ≤ numerator b := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt s_pos) _))
    (termNorm_nonneg _)

/-- Counting-energy coefficient with exactly one support multiplicity. -/
def squaredBound (b : Fin 5) : ℝ :=
  (Nat.choose 4 b.val : ℝ) * numerator b.val ^ 2 / (q - 1) ^ b.val

theorem squaredBound_nonneg (b : Fin 5) : 0 ≤ squaredBound b := by
  unfold squaredBound
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) _)

def activityColumn (j : Fin 14) : Prop := j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3

instance (j : Fin 14) : Decidable (activityColumn j) := by
  unfold activityColumn
  infer_instance

/-- These actual source types have residual degree zero and positive
active count. The vector order itself is unchanged. -/
theorem activityColumn_blockType (j : Fin 14) (h : activityColumn j) :
    (blockType j).1 = 0 ∧ 1 ≤ (blockType j).2 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- Exact rational comparisons follow the separate analytic bound.
First reduce concrete source labels, then expand only the tiny sums. -/
theorem certificate_activity_bounds (j : Fin 14) (h : activityColumn j) :
    0 ≤ lambda * L 13 j ∧
      squaredBound (blockType j).2 ≤ (lambda * L 13 j) ^ 2 := by
  -- Match the accepted scalar proof pattern: Fin constructors precede sums.
  fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | (norm_num [squaredBound, q, Nat.choose, blockType,
        AESRound.Terminal.lambda, AESRound.Certificate.L]
       unfold numerator
       first
         | rw [Fin.sum_univ_two]
         | rw [Fin.sum_univ_three]
         | rw [Fin.sum_univ_four]
         | rw [Fin.sum_univ_succ, Fin.sum_univ_four]
       norm_num [termNorm, q, s, Nat.choose])

end AESConcrete.ActivityCodeScalar
