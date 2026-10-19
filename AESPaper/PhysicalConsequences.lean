import AESPaper.PhysicalView

/-!
Larger round counts and finite independent private information. The
assumed difference bound remains explicit until the AES energy estimates
are supplied; no mixing rate is asserted by these consequences alone.
-/
noncomputable section
open scoped BigOperators
namespace AESMixing.AES

theorem physical_difference_tv_antitone (a : State) :
    Antitone (fun r => tv (physicalDifferenceLaw r a) (uniformExcept (0 : State))) :=
  antitone_nat_of_succ_le (fun r => physical_difference_tv_step r a)

theorem epsilon_lt_at_larger_round (r s : ℕ) (hrs : r ≤ s)
    (eps : ℝ) (heps : 0 < eps)
    (h : ∀ a : State, a ≠ 0 → tv (physicalDifferenceLaw r a) (uniformExcept 0) < eps) :
    epsilon s < eps := by
  apply epsilon_lt_of_difference_bound s eps heps
  intro a ha
  exact lt_of_le_of_lt (physical_difference_tv_antitone a hrs) (h a ha)

theorem physical_private_view_tv_le {R : Type*} [Fintype R]
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (r : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (h : ∀ a : State, a ≠ 0 → tv (physicalDifferenceLaw r a) (uniformExcept 0) ≤ eps)
    (first : R → State) (choose : R → State → State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) (first t) (choose t)))
      (independentView weight (fun t =>
        adaptiveDifferenceView randomPermutationDifference (fun y => choose t y-first t))) ≤ eps := by
  apply tv_independent_view_le weight hw hs
  intro t
  exact physical_adaptive_tv_le r eps heps h (first t) (choose t)

end AESMixing.AES
