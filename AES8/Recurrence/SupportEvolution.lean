/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.SupportProfile
import AESPaper.GroupedRecurrence

/-!
# Exact low/high memory identity for the actual grouped error

The first eleven support coordinates have residual degree at most two; the
last three have residual degree at least three. Their sums split every
zero-extended function. Applying the actual grouped step and substituting the
previous exact error step gives the two-term recurrence used by the numerical
comparison. The second term retains the high projection between two steps.

This module supplies only algebra for the existing grouped AES experiment.
No norm cap, transfer estimate, independence hypothesis, or high-degree
nilpotence is asserted. Constructive proof work only; no attacks,
manuscript changes, or predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
-- Concrete finite AES types exceed the naming linter's recursion depth.
-- This changes only linting; every declaration remains kernel checked.
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.SupportEvolution
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.GroupedRecurrence (step)

/-- The eleven coordinates of residual degrees zero, one, and two. -/
def lowPart (f : WordState → ℝ) : WordState → ℝ :=
  fun x => ∑ c : Fin 11, SupportProfile.component f (Fin.castAdd 3 c) x

/-- The three coordinates of residual degrees three and four. -/
def highPart (f : WordState → ℝ) : WordState → ℝ :=
  fun x => ∑ c : Fin 3, SupportProfile.component f (Fin.natAdd 11 c) x

theorem low_degree (c : Fin 11) :
    SupportProfile.residualDegree (Fin.castAdd 3 c) ≤ 2 := by
  fin_cases c <;> decide

theorem high_degree (c : Fin 3) :
    3 ≤ SupportProfile.residualDegree (Fin.natAdd 11 c) := by
  fin_cases c <;> decide

/-- Pointwise splitting uses the existing full support decomposition, with
the omitted zero-state component removed by the explicit zero-extension premise. -/
theorem split_apply (f : WordState → ℝ) (hf : f 0 = 0) (x : WordState) :
    f x = lowPart f x + highPart f x := by
  calc
    f x = ∑ c : Fin 14, SupportProfile.component f c x :=
      (SupportProfile.component_decomposition f hf x).symm
    _ = lowPart f x + highPart f x :=
      Fin.sum_univ_add (a := 11) (b := 3) (fun c => SupportProfile.component f c x)

theorem split (f : WordState → ℝ) (hf : f 0 = 0) :
    f = lowPart f + highPart f := by
  funext x
  exact split_apply f hf x

/-- Additivity is a direct consequence of the predecessor's exact subtraction
identity, so no separate kernel or execution model is introduced. -/
theorem step_add (f g : WordState → ℝ) : step (f + g) = step f + step g := by
  have h := AESPaper.GroupedRecurrence.step_sub (f + g) g
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

/-- One actual step applied to a split zero-extended input. -/
theorem step_split (f : WordState → ℝ) (hf : f 0 = 0) :
    step f = step (lowPart f) + step (highPart f) := by
  calc
    step f = step (lowPart f + highPart f) := congrArg step (split f hf)
    _ = step (lowPart f) + step (highPart f) := step_add _ _

/-- The complete actual error splits at every grouped time for a nonzero
initial difference. No zero-mass or current-word independence premise is needed. -/
theorem error_split (n : ℕ) (a : AES.State) (ha : a ≠ 0) :
    error n a = lowPart (error n a) + highPart (error n a) :=
  split (error n a) (AESPaper.GroupedLaw.error_zero n a ha)

/-- Exact two-term memory identity. The previous error enters the second
term through `step ∘ highPart ∘ step`, with both boundary permutations retained. -/
theorem error_memory (n : ℕ) (a : AES.State) (ha : a ≠ 0) :
    error (n + 2) a =
      step (lowPart (error (n + 1) a)) +
        step (highPart (step (error n a))) := by
  calc
    error (n + 2) a = step (error (n + 1) a) := by
      simpa only [Nat.add_assoc] using AESPaper.GroupedRecurrence.error_step (n + 1) a
    _ = step (lowPart (error (n + 1) a)) + step (highPart (error (n + 1) a)) :=
      step_split (error (n + 1) a) (AESPaper.GroupedLaw.error_zero (n + 1) a ha)
    _ = step (lowPart (error (n + 1) a)) + step (highPart (step (error n a))) :=
      congrArg (fun f => step (lowPart (error (n + 1) a)) + step (highPart f))
        (AESPaper.GroupedRecurrence.error_step n a)

/-- Indexing aligned with the normalized profile: its index `j` uses
`error (j+1)`, so this is the exact identity behind its later two-step update. -/
theorem actual_memory (j : ℕ) (a : AES.State) (ha : a ≠ 0) :
    error (j + 3) a =
      step (lowPart (error (j + 2) a)) +
        step (highPart (step (error (j + 1) a))) := by
  simpa only [Nat.add_assoc] using error_memory (j + 1) a ha

end AES8.SupportEvolution
