import AESPaper.GroupedRecurrence
import AESPaper.ProfileTV
import AESPaper.PhysicalInterface

/-!
The profile in the conditional numeric theorem is now fixed to the actual AES
law, after removing final ShiftRows and passing to column words. Positivity
and the activity-sensitive TV estimate are proved. The only remaining analytic
premises here are the four-round initialization and repeated matrix comparison.
These premises are not proved merely by defining this concrete profile.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.ConcreteProfile
open AESMixing AESMixing.AES AESPaper.ProfileSpace

def centeredError (n : ℕ) (a : AES.State) : ProfileSpace.State :=
  WithLp.toLp 2 (GroupedLaw.error n a)

theorem centeredError_centered (n : ℕ) (a : AES.State) (ha : a ≠ 0) :
    Centered (centeredError n a) :=
  ⟨GroupedLaw.error_zero n a ha, GroupedLaw.error_sum n a⟩

def physicalProfile (a : AES.State) (k : ℕ) : AESPaper.Profile :=
  normalizedProfile (centeredError (1+2*k) a)

theorem physicalProfile_nonnegative (a : AES.State) (k : ℕ) (i : Fin 5) :
    0 ≤ physicalProfile a k i := normalizedProfile_nonnegative _ i

theorem physicalProfile_tv (a : AES.State) (ha : a ≠ 0) (k : ℕ) :
    tv (physicalDifferenceLaw (4+4*k) a) (uniformExcept 0) ≤
      (1/(2:ℝ)^17) * score (physicalProfile a k) := by
  have hr : 2*(1+2*k)+2 = 4+4*k := by omega
  rw [← hr, GroupedLaw.grouped_tv]
  exact ProfileTV.normalized_tv (centeredError (1+2*k) a)
    (centeredError_centered _ a ha)

theorem epsilon_of_initialization_and_recurrence
    (hinit : ∀ a : AES.State, a ≠ 0 → ∀ i,
      physicalProfile a 0 i ≤ initialEnvelope i)
    (hstep : ∀ a : AES.State, a ≠ 0 → ∀ k i,
      physicalProfile a (k+1) i ≤ step (physicalProfile a k) i)
    (k r : ℕ) (hr : 4+4*k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k :=
  PhysicalInterface.epsilon_of_profiles physicalProfile
    (fun a _ => physicalProfile_nonnegative a) hinit hstep physicalProfile_tv k r hr

theorem private_view_of_initialization_and_recurrence {R : Type*} [Fintype R]
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (hinit : ∀ a : AES.State, a ≠ 0 → ∀ i,
      physicalProfile a 0 i ≤ initialEnvelope i)
    (hstep : ∀ a : AES.State, a ≠ 0 → ∀ k i,
      physicalProfile a (k+1) i ≤ step (physicalProfile a k) i)
    (k r : ℕ) (hr : 4+4*k ≤ r)
    (first : R → AES.State) (choose : R → AES.State → AES.State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) (first t) (choose t)))
      (independentView weight (fun t =>
        adaptiveDifferenceView randomPermutationDifference (fun y => choose t y-first t))) <
      decimalBound k :=
  PhysicalInterface.private_view_of_profiles weight hw hs physicalProfile
    (fun a _ => physicalProfile_nonnegative a) hinit hstep physicalProfile_tv
    k r hr first choose

/-- The paper's actual repeated operator, including both boundary permutations. -/
def fourRound (f : ProfileSpace.State) : ProfileSpace.State :=
  WithLp.toLp 2 (GroupedRecurrence.H (GroupedRecurrence.Pi
    (GroupedRecurrence.H (GroupedRecurrence.Pi (fun x => f x)))))

theorem centeredError_step (a : AES.State) (k : ℕ) :
    centeredError (1+2*(k+1)) a = fourRound (centeredError (1+2*k) a) := by
  have hn : 1+2*(k+1) = (1+2*k)+2 := by omega
  rw [hn]
  exact congrArg (WithLp.toLp 2) (GroupedRecurrence.error_add_two (1+2*k) a)

/-- A uniform operator estimate discharges the sequence recurrence; no profile
or dynamics remains arbitrary in this version of the final interface. -/
theorem epsilon_of_initialization_and_operator
    (hinit : ∀ a : AES.State, a ≠ 0 → ∀ i,
      physicalProfile a 0 i ≤ initialEnvelope i)
    (hoperator : ∀ f : ProfileSpace.State, Centered f → ∀ i,
      normalizedProfile (fourRound f) i ≤ step (normalizedProfile f) i)
    (k r : ℕ) (hr : 4+4*k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k := by
  apply epsilon_of_initialization_and_recurrence hinit ?_ k r hr
  intro a ha j i
  unfold physicalProfile
  rw [centeredError_step]
  exact hoperator _ (centeredError_centered _ a ha) i

end AESPaper.ConcreteProfile
