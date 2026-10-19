import AESPaper.UniformPermutation
import AESPaper.QueryOutput

/-!
# Full uniform-permutation ideal for stopped finite programs
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.FullPermutationOutput
open AESMixing AESPaper.FiniteOutputLaw AESPaper.TwoQueryProgram
open AESPaper.UniformPermutation

section Generic
variable {V R O : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]
  [Fintype R] [Fintype O] [DecidableEq O]

/-- Independent finite seed and one uniformly sampled, retained full permutation.
The operational interpreter makes only the queries selected before stopping. -/
def fullPermutationOutputLaw (weight : R → ℝ) (program : R → Program V O) : O → ℝ :=
  realOutputLaw (fun p : Equiv.Perm V => (p : V → V)) permutationWeight weight program

/-- Exact endpoint identity, including stopping before either query and repeats. -/
theorem fullPermutationOutputLaw_eq_ideal (weight : R → ℝ)
    (program : R → Program V O) :
    fullPermutationOutputLaw weight program = idealOutputLaw weight program := by
  rw [fullPermutationOutputLaw, realOutputLaw_eq_push, idealOutputLaw_eq_push]
  congr 1
  unfold paddedRealView paddedIdealView
  congr 1
  funext t
  exact retainedAdaptiveLaw_eq_adaptiveDifferenceView
    (paddedFirst (program t)) (paddedSecond (program t))

/-- Normalization follows directly from sampling the full finite permutation type. -/
theorem fullPermutationOutputLaw_total (weight : R → ℝ)
    (hs : (∑ t, weight t) = 1) (program : R → Program V O) :
    (∑ o, fullPermutationOutputLaw weight program o) = 1 :=
  realOutputLaw_total _ permutationWeight permutationWeight_total weight hs program

theorem fullPermutationOutputLaw_nonnegative (weight : R → ℝ)
    (hw : ∀ t, 0 ≤ weight t) (program : R → Program V O) (o : O) :
    0 ≤ fullPermutationOutputLaw weight program o := by
  apply realOutputLaw_nonnegative _ permutationWeight _ weight hw program o
  intro p
  unfold permutationWeight
  positivity

end Generic

section AES
variable {R O : Type*} [Fintype R] [Fintype O] [DecidableEq O]

/-- The fixed 14.3 + 73.1k bound against one sampled full uniform permutation. -/
theorem output_tv_bound (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (hs : (∑ t, weight t) = 1) (program : R → Program AES.State O)
    (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    tv (QueryOutput.aesOutputLaw r weight program)
      (fullPermutationOutputLaw weight program) < decimalBound k := by
  rw [fullPermutationOutputLaw_eq_ideal]
  exact QueryOutput.output_tv_bound weight hw hs program k r hr

/-- Arbitrary further finite deterministic postprocessing preserves the bound. -/
theorem postprocessed_tv_bound {Z : Type*} [Fintype Z] [DecidableEq Z]
    (postprocess : O → Z) (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (hs : (∑ t, weight t) = 1) (program : R → Program AES.State O)
    (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    tv (pushLaw postprocess (QueryOutput.aesOutputLaw r weight program))
      (pushLaw postprocess (fullPermutationOutputLaw weight program)) < decimalBound k :=
  lt_of_le_of_lt (tv_pushLaw_le postprocess _ _) (output_tv_bound weight hw hs program k r hr)

end AES
end AESPaper.FullPermutationOutput
