import AESPaper.TwoQueryProgram
import AESPaper.Propagation

/-!
# Finite stopped-query output consequence for the fixed AES target

The private seed is finite, independent of the retained AES keys or ideal
oracle, nonnegative and normalized. It may include private randomness and
arbitrary independent prior information. The seed selects an explicit total
program with zero, one or two adaptive classical forward queries. Its output
type is any finite type, and arbitrary further finite postprocessing is allowed.

Real execution samples the round-key tuple once and runs the stopping program
against the concrete `encrypt r`. Ideal execution uses the explicit lazy
fresh/repeated-answer interpreter. `real_correspondence` and
`ideal_correspondence` identify both laws as the same decoder applied to the
two accepted padded seed/answer views. Data processing then transfers the
proved private-view estimate to the actual stopped output law.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.QueryOutput
open AESMixing AESMixing.AES AESPaper.FiniteOutputLaw AESPaper.TwoQueryProgram

variable {R O : Type*} [Fintype R] [Fintype O] [DecidableEq O]

def aesOutputLaw (r : ℕ) (weight : R → ℝ) (program : R → Program AES.State O) : O → ℝ :=
  realOutputLaw (encrypt r) (uniformKeyWeight (r+1)) weight program

theorem aes_state_card_gt_one : 1 < Fintype.card AES.State := by
  rw [AES.state_card]
  norm_num

theorem aes_key_nonnegative (r : ℕ) (keys : Fin (r+1) → AES.State) :
    0 ≤ uniformKeyWeight (r+1) keys := by
  unfold uniformKeyWeight
  positivity

theorem aes_key_total (r : ℕ) :
    (∑ keys : Fin (r+1) → AES.State, uniformKeyWeight (r+1) keys) = 1 := by
  have hn : (Fintype.card AES.State : ℝ) ≠ 0 := by
    rw [AES.state_card]
    norm_num
  simp only [uniformKeyWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  field_simp [hn]

/-- Real law: one independent seed, one retained key tuple, actual stopping. -/
theorem real_correspondence (r : ℕ) (weight : R → ℝ)
    (program : R → Program AES.State O) :
    aesOutputLaw r weight program =
      pushLaw (outputDecoder program)
        (independentView weight (fun t =>
          retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1))
            (paddedFirst (program t)) (paddedSecond (program t)))) :=
  realOutputLaw_eq_push (encrypt r) (uniformKeyWeight (r+1)) weight program

/-- Ideal law: the stopped lazy interpreter equals exactly the existing
random-permutation-difference private view after the same deterministic decoder. -/
theorem ideal_correspondence (weight : R → ℝ) (program : R → Program AES.State O) :
    idealOutputLaw weight program =
      pushLaw (outputDecoder program)
        (independentView weight (fun t =>
          adaptiveDifferenceView randomPermutationDifference
            (fun y => paddedSecond (program t) y - paddedFirst (program t)))) :=
  idealOutputLaw_eq_push weight program

/-- On distinct fixed inputs, the fresh-answer law agrees with the existing
uniform ordered-distinct-pair reference distribution. Repeats are handled by
the point-mass branch of `freshRepeat`, rather than a distinct-input assumption. -/
theorem ideal_distinct_pair (x x' : AES.State) (hx : x' ≠ x) (y : AES.State × AES.State) :
    freshRepeat x x' y.1 y.2 / Fintype.card AES.State = randomPermutationPair y := by
  rw [freshRepeat, if_neg hx]
  by_cases hy : y.1 = y.2
  · simp [uniformExcept, randomPermutationPair, hy]
  · have hy' : y.2 ≠ y.1 := Ne.symm hy
    simp only [uniformExcept, if_neg hy', randomPermutationPair, if_neg hy,
      AES.state_card, Nat.cast_pow, Nat.cast_ofNat]
    rw [div_div]
    congr 1
    ring

/-- Both direct stopped output laws are probability distributions. -/
theorem output_laws_probability (r : ℕ) (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → Program AES.State O) :
    (∀ o, 0 ≤ aesOutputLaw r weight program o) ∧
      (∑ o, aesOutputLaw r weight program o) = 1 ∧
      (∀ o, 0 ≤ idealOutputLaw weight program o) ∧
      (∑ o, idealOutputLaw weight program o) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact realOutputLaw_nonnegative (encrypt r) (uniformKeyWeight (r+1))
      (aes_key_nonnegative r) weight hw program
  · exact realOutputLaw_total (encrypt r) (uniformKeyWeight (r+1))
      (aes_key_total r) weight hs program
  · exact idealOutputLaw_nonnegative aes_state_card_gt_one weight hw program
  · exact idealOutputLaw_total aes_state_card_gt_one weight hs program

/-- Zero/one/two-query stopping and arbitrary finite output are included by the
program syntax; the proof pads queries only before applying view data processing. -/
theorem output_tv_bound (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (hs : (∑ t, weight t) = 1) (program : R → Program AES.State O)
    (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    tv (aesOutputLaw r weight program) (idealOutputLaw weight program) < decimalBound k := by
  rw [real_correspondence, ideal_correspondence]
  apply lt_of_le_of_lt (tv_pushLaw_le (outputDecoder program) _ _) ?_
  exact Propagation.private_view weight hw hs k r hr
    (fun t => paddedFirst (program t)) (fun t => paddedSecond (program t))

/-- Any additional deterministic finite output transformation preserves the
same strict bound. Additional finite coins may be included in the private seed. -/
theorem postprocessed_tv_bound {Z : Type*} [Fintype Z] [DecidableEq Z]
    (postprocess : O → Z) (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (hs : (∑ t, weight t) = 1) (program : R → Program AES.State O)
    (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    tv (pushLaw postprocess (aesOutputLaw r weight program))
      (pushLaw postprocess (idealOutputLaw weight program)) < decimalBound k :=
  lt_of_le_of_lt (tv_pushLaw_le postprocess _ _)
    (output_tv_bound weight hw hs program k r hr)

end AESPaper.QueryOutput
