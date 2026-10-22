import AES8.Consequences.PaperAESKS07Estimates
import AES8.Probability.PaperAdaptive

/-!
# Named current-paper consequences from the explicit KS07 premises

Source candidate, 2026-10-22, for paper commit 1906c42e. This leaf exposes the
literal profile recurrence, parity/tail bounds, exact mixing family and stated
round corollaries, reusing the passing `PaperAESFromKS07` endpoint. The final
wrapper composes the paper's adaptive reduction with that numerical family.

Every external-dependent theorem takes `KS07Bounds` explicitly. All laws are
the existing AES experiment: independent round keys sampled once and retained,
the paper's whitening, and at most two adaptive classical forward queries.
No premise is constructed and no standard-key-schedule or higher-query claim
is introduced. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESKS07Named
open AESMixing AESMixing.AES PaperComparison
open PaperAESKS07Estimates
open PaperKS07AssumedEntries (KS07Bounds)
set_option autoImplicit false

/-- Paper prop:normalized-profile, with the literal j>=1 memory clause. -/
theorem normalized_profile (hKS : KS07Bounds) (a : AES.State) (ha : a ≠ 0) :
    (NormalizedProfile.actual a 0 ≤ scale 1000 (realProfile startup0)) ∧
    (NormalizedProfile.actual a 1 ≤ fun i =>
      AESRound.matVec realStep (NormalizedProfile.actual a 0) i +
        1000 * realProfile firstReturn i) ∧
    (∀ j : ℕ, 1 ≤ j → NormalizedProfile.actual a (j+1) ≤ fun i =>
      AESRound.matVec realStep (NormalizedProfile.actual a j) i +
        AESRound.matVec realReturn (NormalizedProfile.actual a (j-1)) i) ∧
    (∀ j : ℕ,
      tv (physicalDifferenceLaw (4+2*j) a) (uniformExcept (0 : AES.State)) ≤
        (1 / 2^(17 : ℕ) : ℝ) * omega41^j *
          PaperPhysicalOutput.Phi (NormalizedProfile.actual a j)) := by
  have htransfer := PaperCurrentRecurrence.actual_transfer (profile_estimates hKS)
  refine ⟨PaperCurrentRecurrence.actual_initial (profile_estimates hKS) a ha,
    htransfer.first a ha, ?_, fun j => PaperNormalizedOutput.actual_output a ha j⟩
  intro j hj
  have h := htransfer.step a ha (j-1)
  have hi : j-1+1 = j := by omega
  have ho : j-1+2 = j+1 := by omega
  simpa only [hi, ho] using h

/-- Paper lem:parity-profiles for every k>=1. -/
theorem parity_profiles (hKS : KS07Bounds) (a : AES.State) (ha : a ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    NormalizedProfile.actual a (2*k) ≤ scale 1000 PaperOutputEnvelopes.evenEnvelope ∧
    NormalizedProfile.actual a (2*k+1) ≤ scale 1000 PaperOutputEnvelopes.oddEnvelope :=
  PaperAESFromKS07.parity_profiles hKS a ha k hk

/-- Paper lem:tail, including the strict bound for every j>=2. -/
theorem tail (hKS : KS07Bounds) (a : AES.State) (ha : a ≠ 0)
    (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) < 112 :=
  PaperAESFromKS07.tail hKS a ha j hj

/-- Paper thm:main with its exact factor seven. -/
theorem epsilon_eight_plus_two (hKS : KS07Bounds) (k : ℕ) :
    AES.epsilon (8+2*k) < 7 / (2 : ℝ)^(95+41*k) :=
  PaperAESFromKS07.epsilon_eight_plus_two hKS k

/-- At ten rounds 7/2^136 is strictly below 2^-133. -/
theorem ten_round_exact (hKS : KS07Bounds) :
    AES.epsilon 10 < (1 : ℝ)/2^(133 : ℕ) :=
  (epsilon_eight_plus_two hKS 1).trans (by norm_num)

/-- At fourteen rounds 7/2^218 is strictly below 2^-215. -/
theorem fourteen_round_exact (hKS : KS07Bounds) :
    AES.epsilon 14 < (1 : ℝ)/2^(215 : ℕ) :=
  (epsilon_eight_plus_two hKS 3).trans (by norm_num)

/-- At sixteen rounds 7/2^259 is strictly below 2^-256. -/
theorem sixteen_round_256 (hKS : KS07Bounds) :
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  (PaperAESFromKS07.round_corollaries hKS).2.2

/-- Paper cor:rounds, retaining its exact 133/215 intermediate comparisons. -/
theorem round_corollaries_exact (hKS : KS07Bounds) :
    AES.epsilon 10 < (1 : ℝ)/2^(133 : ℕ) ∧
    (1 : ℝ)/2^(133 : ℕ) < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(215 : ℕ) ∧
    (1 : ℝ)/2^(215 : ℕ) < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  ⟨ten_round_exact hKS, by norm_num, fourteen_round_exact hKS,
    by norm_num, sixteen_round_256 hKS⟩

/-- The sufficient-round interface follows from the sharper corollary. -/
theorem round_corollaries (hKS : KS07Bounds) :
    AES.epsilon 10 < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  ⟨(ten_round_exact hKS).trans (by norm_num),
    (fourteen_round_exact hKS).trans (by norm_num), sixteen_round_256 hKS⟩

/-- Numeric consequence of paper lem:adaptive and thm:main. The program
syntax permits stopping before either query and repeated queries, with an
independent finite private seed and arbitrary finite output. -/
theorem adaptive_program_output_lt {R O : Type*}
    [Fintype R] [Fintype O] [DecidableEq O]
    (hKS : KS07Bounds) (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → AESPaper.TwoQueryProgram.Program AES.State O) (k : ℕ) :
    tv (AESPaper.TwoQueryProgram.realOutputLaw (AES.encrypt (8+2*k))
        (uniformKeyWeight (8+2*k+1)) weight program)
      (AESPaper.TwoQueryProgram.realOutputLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        AESPaper.UniformPermutation.permutationWeight weight program) <
      7 / (2 : ℝ)^(95+41*k) :=
  (PaperAdaptive.program_tv_le_epsilon (8+2*k) weight hw hs program).trans_lt
    (epsilon_eight_plus_two hKS k)

#print axioms normalized_profile
#print axioms parity_profiles
#print axioms tail
#print axioms epsilon_eight_plus_two
#print axioms ten_round_exact
#print axioms fourteen_round_exact
#print axioms sixteen_round_256
#print axioms round_corollaries_exact
#print axioms round_corollaries
#print axioms adaptive_program_output_lt
end AES8.PaperAESKS07Named
