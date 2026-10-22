import AESConcrete.ActivityMinor

/-!
# Common-moment envelopes for activity minor aggregation

New candidate definitions only. Accepted ActivityMinor sources remain frozen.
The scalar formulas become operator bounds only after actual contractions,
signed input expansion, and physical support aggregation are proved.
Constructive mathematics only; no attacks or manuscript changes. Preserve
independent retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target. No full theorem is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinorEnvelope
open AESConcrete.ActivityCodeScalar (q s)
open AESConcrete.RefinedStepZeros (blockType)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A common squared moment for every nontrivial minor of the retained length. -/
def moment (d : ℕ) : ℝ := if d = 2 then 90000 / q ^ 3 else 12000 / q ^ 4

/-- Absolute omitted-leg weights, grouped by the number of full-uniform choices.
The inequalities exclude both exactly vanishing endpoint dimensions. -/
def omittedSum (d a t : ℕ) : ℝ :=
  ∑ u : Fin (a - d + 1),
    if 4 - d - u.val < t ∧ t < 4 - u.val then
      (Nat.choose (a - d) u.val : ℝ) * s ^ u.val else 0

/-- Exact common norm factor; its square will retain the full moment. -/
def termNorm (d a t : ℕ) : ℝ :=
  Real.sqrt (moment d) / (s ^ (4 - d) * Real.sqrt (q - 1) ^ (a - d)) *
    omittedSum d a t

/-- Signed source expansion is bounded by this absolute weighted sum. -/
def inputNumerator (d a b : ℕ) : ℝ :=
  ∑ t : Fin (b + 1), (Nat.choose b t.val : ℝ) * s ^ t.val * omittedSum d a t.val

/-- One input support and one selected physical output, before multiplicities. -/
def pieceBound (d a b : ℕ) : ℝ :=
  moment d * inputNumerator d a b ^ 2 /
    (s ^ (2 * (4 - d)) * (q - 1) ^ (a - d + b))

theorem moment_nonneg (d : ℕ) : 0 ≤ moment d := by
  unfold moment q
  split_ifs <;> positivity

theorem omittedSum_nonneg (d a t : ℕ) : 0 ≤ omittedSum d a t := by
  unfold omittedSum s
  apply Finset.sum_nonneg
  intro u _
  split_ifs <;> positivity

theorem termNorm_nonneg (d a t : ℕ) : 0 ≤ termNorm d a t := by
  unfold termNorm
  exact mul_nonneg (by unfold s; positivity) (omittedSum_nonneg d a t)

theorem pieceBound_nonneg (d a b : ℕ) : 0 ≤ pieceBound d a b := by
  unfold pieceBound
  exact div_nonneg (mul_nonneg (moment_nonneg d) (sq_nonneg _)) (by
    unfold q s
    positivity)

/-- Exact finite simplification of the two independent support multiplicities.
This scalar identity does not establish any physical energy bound. -/
theorem physicalEnvelope_eq (i j : Fin 14) (h : ActivityMinorScalar.minorPair i j) :
    (Fintype.card (SelectedSupport (blockType i).1 (blockType i).2) : ℝ) *
      (Nat.choose 4 (blockType j).2.val : ℝ) *
      pieceBound (blockType i).1.val (blockType i).2.val (blockType j).2.val =
        ActivityMinorScalar.squaredBound i (blockType j).2 := by
  have hvalid : ∀ k : Fin 14, (blockType k).1 ≤ (blockType k).2 := by decide
  rw [ResidualIncidenceCoefficient.selectedSupport_card _ _ (hvalid i)]
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | (norm_num [ResidualIncidenceCoefficient.multiplicity, pieceBound,
        moment, ActivityMinorScalar.squaredBound,
        q, s, Nat.choose, blockType, Fin.ext_iff]
       unfold inputNumerator omittedSum
       repeat first
         | rw [Fin.sum_univ_two]
         | rw [Fin.sum_univ_three]
         | rw [Fin.sum_univ_four]
         | rw [Fin.sum_univ_succ]
       norm_num [q, s, Nat.choose])

end AESConcrete.ActivityMinorEnvelope
