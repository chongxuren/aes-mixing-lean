/- Module role: Conditional concrete AES and adaptive-query consequences of the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.Theorem
import AESPaper.PhysicalConsequences
import AESPaper.GroupedRecurrence
import AESPaper.UniformPermutation

/-!
# Conditional bridge to the concrete retained-key AES experiment

The experiment, physical difference law, grouped error, and full-permutation
reference are the actual vendored objects. `DifferenceProfileBounds` leaves
the AES-specific initialization, recurrence, and profile-to-TV estimates
explicit for every nonzero initial difference. This module does not discharge
those analytic obligations or assert the unconditional AES mixing theorem.

The operational consequence allows finite independent private information and
finite outputs, with zero, one, or two adaptive classical forward queries,
including repeats. Its exported TV bound is non-strict; the concrete pairwise
epsilon bound is strict. Constructive proof work only; no attacks or manuscript
changes. No predecessor source is modified.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.ConcreteBridge
open AESMixing AESMixing.AES
open AESPaper.FiniteOutputLaw AESPaper.TwoQueryProgram AESPaper.UniformPermutation

/-- The target written with a natural-number exponent. -/
def dyadicBound (k : ℕ) : ℝ := (1 : ℝ) / 2 ^ (92 + 41 * k)

theorem dyadicBound_pos (k : ℕ) : 0 < dyadicBound k := by
  unfold dyadicBound
  positivity

/-- Genuine remaining analytic requirements, indexed by the initial difference.
No hypothesis here assumes a final bound on `AES.epsilon`. -/
def DifferenceProfileBounds (z : AES.State → ℕ → AES8.Profile) : Prop :=
  ∀ a : AES.State, a ≠ 0 →
    AES8.ProfileBounds
      (fun r => tv (physicalDifferenceLaw r a) (uniformExcept (0 : AES.State)))
      (z a)

/-- The grouped error at index `j+1` is the physical error at round `4+2*j`.
The absolute-value sum uses counting measure, matching half-l1 TV exactly. -/
theorem grouped_error_tv (j : ℕ) (a : AES.State) :
    tv (physicalDifferenceLaw (4 + 2 * j) a) (uniformExcept (0 : AES.State)) =
      (∑ x, |AESPaper.GroupedLaw.error (j + 1) a x|) / 2 := by
  have hround : 2 * (j + 1) + 2 = 4 + 2 * j := by omega
  simpa only [hround] using AESPaper.GroupedLaw.grouped_tv (j + 1) a

variable {z : AES.State → ℕ → AES8.Profile}

theorem difference_eight_plus_two (hb : DifferenceProfileBounds z)
    (k : ℕ) (a : AES.State) (ha : a ≠ 0) :
    tv (physicalDifferenceLaw (8 + 2 * k) a) (uniformExcept (0 : AES.State)) <
      dyadicBound k :=
  AES8.eight_plus_two (hb a ha) k

theorem difference_at_larger_round (hb : DifferenceProfileBounds z)
    (k r : ℕ) (hr : 8 + 2 * k ≤ r) (a : AES.State) (ha : a ≠ 0) :
    tv (physicalDifferenceLaw r a) (uniformExcept (0 : AES.State)) <
      dyadicBound k :=
  lt_of_le_of_lt (physical_difference_tv_antitone a hr)
    (difference_eight_plus_two hb k a ha)

/-- Conditional concrete pairwise result for the independent uniform retained-key
experiment, including whitening and omitted final MixColumns. -/
theorem epsilon_eight_plus_two (hb : DifferenceProfileBounds z) (k : ℕ) :
    AES.epsilon (8 + 2 * k) < dyadicBound k := by
  apply epsilon_lt_of_difference_bound (8 + 2 * k) (dyadicBound k)
    (dyadicBound_pos k)
  exact fun a ha => difference_eight_plus_two hb k a ha

theorem epsilon_at_larger_round (hb : DifferenceProfileBounds z)
    (k r : ℕ) (hr : 8 + 2 * k ≤ r) :
    AES.epsilon r < dyadicBound k :=
  epsilon_lt_at_larger_round (8 + 2 * k) r hr (dyadicBound k)
    (dyadicBound_pos k) (fun a ha => difference_eight_plus_two hb k a ha)

theorem ten_round_exact (hb : DifferenceProfileBounds z) :
    AES.epsilon 10 < (1 : ℝ) / 2 ^ (133 : ℕ) := by
  simpa only [dyadicBound] using epsilon_eight_plus_two hb 1

theorem ten_round_128 (hb : DifferenceProfileBounds z) :
    AES.epsilon 10 < (1 : ℝ) / 2 ^ (128 : ℕ) :=
  lt_trans (ten_round_exact hb) (by norm_num)

theorem fourteen_round_exact (hb : DifferenceProfileBounds z) :
    AES.epsilon 14 < (1 : ℝ) / 2 ^ (215 : ℕ) := by
  simpa only [dyadicBound] using epsilon_eight_plus_two hb 3

theorem fourteen_round_192 (hb : DifferenceProfileBounds z) :
    AES.epsilon 14 < (1 : ℝ) / 2 ^ (192 : ℕ) :=
  lt_trans (fourteen_round_exact hb) (by norm_num)

theorem sixteen_round_256 (hb : DifferenceProfileBounds z) :
    AES.epsilon 16 < (1 : ℝ) / 2 ^ (256 : ℕ) := by
  simpa only [dyadicBound] using epsilon_eight_plus_two hb 4

/-- Two adaptive forward answers, including repeated inputs, against the exact
lazy difference view. No distinct-query hypothesis is imposed. -/
theorem adaptive_difference_view_tv_le (hb : DifferenceProfileBounds z)
    (k r : ℕ) (hr : 8 + 2 * k ≤ r) (x : AES.State)
    (choose : AES.State → AES.State) :
    tv (retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r + 1)) x choose)
      (adaptiveDifferenceView randomPermutationDifference (fun y => choose y - x)) ≤
      dyadicBound k :=
  physical_adaptive_tv_le r (dyadicBound k) (dyadicBound_pos k).le
    (fun a ha => (difference_at_larger_round hb k r hr a ha).le) x choose

/-- The ideal samples one uniformly random full permutation and retains it for
both answers. The existing exact sampler identity introduces no TV loss. -/
theorem full_permutation_view_tv_le (hb : DifferenceProfileBounds z)
    (k r : ℕ) (hr : 8 + 2 * k ≤ r) (x : AES.State)
    (choose : AES.State → AES.State) :
    tv (retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r + 1)) x choose)
      (retainedAdaptiveLaw (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
        permutationWeight x choose) ≤ dyadicBound k := by
  have hideal :
      retainedAdaptiveLaw (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
          permutationWeight x choose =
        adaptiveDifferenceView randomPermutationDifference (fun y => choose y - x) :=
    retainedAdaptiveLaw_eq_adaptiveDifferenceView x choose
  rw [hideal]
  exact adaptive_difference_view_tv_le hb k r hr x choose

section PrivateInformation
variable {R : Type*} [Fintype R]

/-- An independent finite private seed is retained in the complete answer view. -/
theorem private_full_permutation_view_tv_le (hb : DifferenceProfileBounds z)
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (k r : ℕ) (hr : 8 + 2 * k ≤ r) (first : R → AES.State)
    (choose : R → AES.State → AES.State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r + 1)) (first t) (choose t)))
      (independentView weight (fun t =>
        retainedAdaptiveLaw (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
          permutationWeight (first t) (choose t))) ≤ dyadicBound k := by
  apply tv_independent_view_le weight hw hs
  intro t
  exact full_permutation_view_tv_le hb k r hr (first t) (choose t)

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- Direct stopped execution against one independently sampled retained key tuple. -/
def aesOutputLaw (r : ℕ) (weight : R → ℝ)
    (program : R → Program AES.State O) : O → ℝ :=
  realOutputLaw (encrypt r) (uniformKeyWeight (r + 1)) weight program

/-- The same stopped execution against one sampled retained full permutation. -/
def fullPermutationOutputLaw (weight : R → ℝ)
    (program : R → Program AES.State O) : O → ℝ :=
  realOutputLaw (fun p : Equiv.Perm AES.State => (p : AES.State → AES.State))
    permutationWeight weight program

/-- The program makes at most two queries by its syntax, and may stop before
either query. Decoder data processing transfers the complete answer-view bound. -/
theorem program_output_tv_le (hb : DifferenceProfileBounds z)
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → Program AES.State O) (k r : ℕ) (hr : 8 + 2 * k ≤ r) :
    tv (aesOutputLaw r weight program) (fullPermutationOutputLaw weight program) ≤
      dyadicBound k := by
  rw [aesOutputLaw, fullPermutationOutputLaw,
    realOutputLaw_eq_push, realOutputLaw_eq_push]
  exact (tv_pushLaw_le (outputDecoder program) _ _).trans
    (private_full_permutation_view_tv_le hb weight hw hs k r hr
      (fun t => paddedFirst (program t)) (fun t => paddedSecond (program t)))

theorem postprocessed_output_tv_le {Z : Type*} [Fintype Z] [DecidableEq Z]
    (hb : DifferenceProfileBounds z) (postprocess : O → Z)
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (program : R → Program AES.State O) (k r : ℕ) (hr : 8 + 2 * k ≤ r) :
    tv (pushLaw postprocess (aesOutputLaw r weight program))
      (pushLaw postprocess (fullPermutationOutputLaw weight program)) ≤
      dyadicBound k :=
  (tv_pushLaw_le postprocess _ _).trans
    (program_output_tv_le hb weight hw hs program k r hr)

end PrivateInformation
end AES8.ConcreteBridge
