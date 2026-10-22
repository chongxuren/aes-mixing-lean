/- Module role: Retained-key experiment and adaptive-query reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESPaper.PhysicalConsequences
import AESPaper.UniformPermutation
import AESPaper.TwoQueryProgram

/-!
# Paper Lemma 1: two adaptive queries, with the exact pairwise parameter

The bound is the existing physical `AES.epsilon r`, with no assumed mixing
estimate and no numerical recurrence. Round keys are sampled once and retained;
the ideal samples one full permutation and retains it. The program semantics
permit stopping before either query, repeated queries, independent finite private
coins, and arbitrary finite output postprocessing.

The proof follows the paper: dominate every nonzero difference distance by the
maximum pair distance, condition on the first answer and private seed, then use
deterministic data processing. The underlying exact experiment identities are
reused from the checked predecessor. No manuscript or predecessor is changed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperAdaptive
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open AESMixing AESMixing.AES
open AESPaper.FiniteOutputLaw AESPaper.TwoQueryProgram AESPaper.UniformPermutation

theorem epsilon_nonneg (r : ℕ) : 0 ≤ AES.epsilon r := by
  have h := Finset.le_sup'
    (fun inputs : AES.State × AES.State =>
      if inputs.1 = inputs.2 then (0 : ℝ)
      else tv (pairLaw r inputs.1 inputs.2) randomPermutationPair)
    (Finset.mem_univ ((0 : AES.State), (0 : AES.State)))
  simpa only [Prod.fst, Prod.snd, ite_true, AES.epsilon] using h

theorem pair_tv_le_epsilon (r : ℕ) (x x' : AES.State) (hxx' : x ≠ x') :
    tv (pairLaw r x x') randomPermutationPair ≤ AES.epsilon r := by
  have h := Finset.le_sup'
    (fun inputs : AES.State × AES.State =>
      if inputs.1 = inputs.2 then (0 : ℝ)
      else tv (pairLaw r inputs.1 inputs.2) randomPermutationPair)
    (Finset.mem_univ (x, x'))
  simpa only [Prod.fst, Prod.snd, if_neg hxx', AES.epsilon] using h

theorem difference_tv_le_epsilon (r : ℕ) (a : AES.State) (ha : a ≠ 0) :
    tv (physicalDifferenceLaw r a) (uniformExcept (0 : AES.State)) ≤
      AES.epsilon r := by
  have h := pair_tv_le_epsilon r 0 a (Ne.symm ha)
  simpa only [physical_pair_tv, sub_zero] using h

/-- Exact retained answer-pair law, allowing an arbitrary adaptive second input. -/
theorem adaptive_view_tv_le_epsilon (r : ℕ) (x : AES.State)
    (choose : AES.State → AES.State) :
    tv (retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r + 1)) x choose)
      (retainedAdaptiveLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight x choose) ≤ AES.epsilon r := by
  have hideal :
      retainedAdaptiveLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight x choose =
      adaptiveDifferenceView randomPermutationDifference (fun y => choose y - x) :=
    retainedAdaptiveLaw_eq_adaptiveDifferenceView x choose
  rw [hideal]
  exact physical_adaptive_tv_le r (AES.epsilon r) (epsilon_nonneg r)
    (difference_tv_le_epsilon r) x choose

section PrivateSeed
variable {R : Type*} [Fintype R]

theorem private_view_tv_le_epsilon (r : ℕ) (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (first : R → AES.State) (choose : R → AES.State → AES.State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r + 1))
          (first t) (choose t)))
      (independentView weight (fun t =>
        retainedAdaptiveLaw
          (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
          permutationWeight (first t) (choose t))) ≤ AES.epsilon r := by
  apply tv_independent_view_le weight hw hs
  intro t
  exact adaptive_view_tv_le_epsilon r (first t) (choose t)

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- Paper Lemma 1 for every operational program making at most two queries.
Taking its output to encode the complete transcript gives the transcript claim. -/
theorem program_tv_le_epsilon (r : ℕ) (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → Program AES.State O) :
    tv (realOutputLaw (encrypt r) (uniformKeyWeight (r + 1)) weight program)
      (realOutputLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight weight program) ≤ AES.epsilon r := by
  rw [realOutputLaw_eq_push, realOutputLaw_eq_push]
  exact (tv_pushLaw_le (outputDecoder program) _ _).trans
    (private_view_tv_le_epsilon r weight hw hs
      (fun t => paddedFirst (program t)) (fun t => paddedSecond (program t)))

theorem postprocessed_tv_le_epsilon {Z : Type*} [Fintype Z] [DecidableEq Z]
    (r : ℕ) (postprocess : O → Z) (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → Program AES.State O) :
    tv (pushLaw postprocess
        (realOutputLaw (encrypt r) (uniformKeyWeight (r + 1)) weight program))
      (pushLaw postprocess (realOutputLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight weight program)) ≤ AES.epsilon r :=
  (tv_pushLaw_le postprocess _ _).trans
    (program_tv_le_epsilon r weight hw hs program)

/-- The three constructors record exactly zero, one or two queries, followed
by the terminal output. No padded query or answer appears in this type. -/
abbrev Transcript (V O : Type*) :=
  O ⊕ ((V × V × O) ⊕ (V × V × V × V × O))

def recordContinuation (t : R) (x y : AES.State) :
    Continuation AES.State O → Continuation AES.State (R × Transcript AES.State O)
  | .stop o => .stop (t, .inr (.inl (x, y, o)))
  | .query x' finish =>
      .query x' (fun y' => (t, .inr (.inr (x, y, x', y', finish y'))))

/-- The same stopping and query decisions, with the seed and actual transcript
recorded in the terminal output. -/
def recordProgram (t : R) :
    Program AES.State O → Program AES.State (R × Transcript AES.State O)
  | .stop o => .stop (t, .inl o)
  | .query x next => .query x (fun y => recordContinuation t x y (next y))

theorem recordProgram_queryCount (t : R) (p : Program AES.State O)
    (oracle : AES.State → AES.State) :
    queryCount (recordProgram t p) oracle = queryCount p oracle := by
  cases p with
  | stop o => rfl
  | query x next =>
      cases h : next (oracle x) <;>
        simp [recordProgram, recordContinuation, queryCount, continuationQueries, h]

def transcriptOutput : Transcript AES.State O → O
  | .inl o => o
  | .inr (.inl (_, _, o)) => o
  | .inr (.inr (_, _, _, _, o)) => o

theorem recordProgram_output (t : R) (p : Program AES.State O)
    (oracle : AES.State → AES.State) :
    transcriptOutput (run (recordProgram t p) oracle).2 = run p oracle := by
  cases p with
  | stop o => rfl
  | query x next =>
      cases h : next (oracle x) <;>
        simp [recordProgram, recordContinuation, run, runContinuation,
          transcriptOutput, h]

/-- Literal complete stopped views: the seed, actual query-answer pairs, and
terminal output, with the same retained oracle on both active calls. -/
theorem complete_view_tv_le_epsilon [DecidableEq R]
    (r : ℕ) (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (hs : (∑ t, weight t) = 1) (program : R → Program AES.State O) :
    tv (realOutputLaw (encrypt r) (uniformKeyWeight (r + 1)) weight
        (fun t => recordProgram t (program t)))
      (realOutputLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight weight (fun t => recordProgram t (program t))) ≤
      AES.epsilon r :=
  program_tv_le_epsilon r weight hw hs (fun t => recordProgram t (program t))

end PrivateSeed
end AES8.PaperAdaptive
