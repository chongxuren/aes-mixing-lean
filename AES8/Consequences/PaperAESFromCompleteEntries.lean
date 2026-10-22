import AES8.Estimates.Transfer.PaperAESCompleteEstimates
import AES8.Consequences.PaperAESProfilesFromEntries
import AES8.Probability.PaperAdaptive

/-!
# Current profile and mixing consequences of the complete inventory

Resources, physical estimates, and named consequences have distinct consumer
leaves. The exact main theorem and adaptive corollary have no finite or physical
premise.

All laws use the actual AES experiment: independent uniform round keys sampled
once and retained, initial whitening and omitted final MixColumns. The program
corollary covers at most two adaptive classical forward queries, with optional
stopping, repeated queries and independent finite private randomness.

This route proves the sufficient consumed entry bounds, not KS07 exact maxima.
No standard-key-schedule or higher-query guarantee is asserted.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESFromCompleteEntries
open AESMixing AESMixing.AES PaperComparison PaperAESCompleteResources
open PaperAESCompleteEstimates
set_option autoImplicit false

/-- Paper prop:normalized-profile, with the literal j>=1 recurrence clause. -/
theorem normalized_profile (a : AES.State) (ha : a ≠ 0) :
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
  have htransfer := PaperCurrentRecurrence.actual_transfer profile_estimates
  refine ⟨PaperCurrentRecurrence.actual_initial profile_estimates a ha,
    htransfer.first a ha, ?_, fun j => PaperNormalizedOutput.actual_output a ha j⟩
  intro j hj
  have h := htransfer.step a ha (j-1)
  have hi : j-1+1 = j := by omega
  have ho : j-1+2 = j+1 := by omega
  simpa only [hi, ho] using h

/-- Paper lem:parity-profiles, with both current bounds for every k>=1. -/
theorem parity_profiles (a : AES.State) (ha : a ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    NormalizedProfile.actual a (2*k) ≤ scale 1000 PaperOutputEnvelopes.evenEnvelope ∧
    NormalizedProfile.actual a (2*k+1) ≤ scale 1000 PaperOutputEnvelopes.oddEnvelope :=
  PaperAESProfilesFromEntries.parity_profiles ordinary_raw_bound fourier_raw_bound a ha k hk

/-- Paper lem:tail, with the strict current 112 bound for every j>=2. -/
theorem tail (a : AES.State) (ha : a ≠ 0) (j : ℕ) (hj : 2 ≤ j) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) < 112 :=
  PaperAESProfilesFromEntries.tail ordinary_raw_bound fourier_raw_bound a ha j hj

/-- Paper thm:main: the exact 7/8 improvement over the historical bound. -/
theorem epsilon_eight_plus_two (k : ℕ) :
    AES.epsilon (8+2*k) < 7 / (2 : ℝ)^(95+41*k) :=
  PaperAESFromEntries.epsilon_eight_plus_two ordinary_raw_bound fourier_raw_bound k

/-- At 10 rounds the common bound is 7/2^136, strictly below 2^-133. -/
theorem ten_round_exact : AES.epsilon 10 < (1 : ℝ)/2^(133 : ℕ) :=
  (epsilon_eight_plus_two 1).trans (by norm_num)

/-- At 14 rounds the common bound is 7/2^218, strictly below 2^-215. -/
theorem fourteen_round_exact : AES.epsilon 14 < (1 : ℝ)/2^(215 : ℕ) :=
  (epsilon_eight_plus_two 3).trans (by norm_num)

/-- At 16 rounds 7/2^259 is strictly below 2^-256. -/
theorem sixteen_round_256 : AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  (epsilon_eight_plus_two 4).trans (by
    rw [show (95 + 41 * 4 : ℕ) = 256 + 3 by decide, pow_add]
    norm_num)

/-- Paper cor:rounds, including its exact 133/215 intermediate comparisons. -/
theorem round_corollaries_exact :
    AES.epsilon 10 < (1 : ℝ)/2^(133 : ℕ) ∧
    (1 : ℝ)/2^(133 : ℕ) < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(215 : ℕ) ∧
    (1 : ℝ)/2^(215 : ℕ) < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  ⟨ten_round_exact, by norm_num, fourteen_round_exact, by norm_num, sixteen_round_256⟩

/-- The standard sufficient-round interface follows from the sharper row. -/
theorem round_corollaries :
    AES.epsilon 10 < (1 : ℝ)/2^(128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ)/2^(192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ)/2^(256 : ℕ) :=
  ⟨ten_round_exact.trans (by norm_num),
    fourteen_round_exact.trans (by norm_num), sixteen_round_256⟩

/-- Numeric consequence of paper lem:adaptive and thm:main. The program
syntax permits stopping before either query and repeated queries, with an
independent finite private seed and arbitrary finite output. -/
theorem adaptive_program_output_lt {R O : Type*}
    [Fintype R] [Fintype O] [DecidableEq O]
    (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → AESPaper.TwoQueryProgram.Program AES.State O) (k : ℕ) :
    tv (AESPaper.TwoQueryProgram.realOutputLaw (AES.encrypt (8+2*k))
        (uniformKeyWeight (8+2*k+1)) weight program)
      (AESPaper.TwoQueryProgram.realOutputLaw
        (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        AESPaper.UniformPermutation.permutationWeight weight program) <
      7 / (2 : ℝ)^(95+41*k) :=
  (PaperAdaptive.program_tv_le_epsilon (8+2*k) weight hw hs program).trans_lt
    (epsilon_eight_plus_two k)


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
end AES8.PaperAESFromCompleteEntries
