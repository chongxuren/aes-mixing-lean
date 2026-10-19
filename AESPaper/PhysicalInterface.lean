import AESPaper.Comparison
import AESPaper.PhysicalConsequences

/-!
Conditional connection to the concrete retained-key AES experiment.
The normalized profile estimates remain hypotheses for each nonzero input.
The imported physical law supplies whitening, omitted final MixColumns and
monotonicity for additional rounds. The private-view corollary covers finite
independent private information and two adaptive forward answers, including
repeated queries. A complete stopping/output postprocessing theorem is separate.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AESPaper.PhysicalInterface
open AESMixing AESMixing.AES
noncomputable section

theorem difference_of_profiles
    (z : State → ℕ → Profile)
    (hz : ∀ a, a ≠ 0 → ∀ k i, 0 ≤ z a k i)
    (hinit : ∀ a, a ≠ 0 → ∀ i, z a 0 i ≤ initialEnvelope i)
    (hstep : ∀ a, a ≠ 0 → ∀ k i, z a (k+1) i ≤ step (z a k) i)
    (htv : ∀ a, a ≠ 0 → ∀ k,
      tv (physicalDifferenceLaw (4+4*k) a) (uniformExcept 0) ≤
        (1/2^17 : ℝ) * score (z a k))
    (k r : ℕ) (hr : 4+4*k ≤ r) (a : State) (ha : a ≠ 0) :
    tv (physicalDifferenceLaw r a) (uniformExcept 0) < rationalBound k :=
  (mixing_bound_of_profiles
    (fun s => tv (physicalDifferenceLaw s a) (uniformExcept 0)) (z a)
    (hz a ha) (hinit a ha) (hstep a ha) (htv a ha)
    (physical_difference_tv_antitone a) k r hr).1

theorem epsilon_of_profiles
    (z : State → ℕ → Profile)
    (hz : ∀ a, a ≠ 0 → ∀ k i, 0 ≤ z a k i)
    (hinit : ∀ a, a ≠ 0 → ∀ i, z a 0 i ≤ initialEnvelope i)
    (hstep : ∀ a, a ≠ 0 → ∀ k i, z a (k+1) i ≤ step (z a k) i)
    (htv : ∀ a, a ≠ 0 → ∀ k,
      tv (physicalDifferenceLaw (4+4*k) a) (uniformExcept 0) ≤
        (1/2^17 : ℝ) * score (z a k))
    (k r : ℕ) (hr : 4+4*k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k := by
  refine ⟨?_, rational_lt_decimal k⟩
  apply epsilon_lt_of_difference_bound r (rationalBound k)
    (mul_pos initialCoefficient_pos (pow_pos blockRate_pos k))
  exact difference_of_profiles z hz hinit hstep htv k r hr

theorem private_view_of_profiles {R : Type*} [Fintype R]
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t) (hs : (∑ t, weight t) = 1)
    (z : State → ℕ → Profile)
    (hz : ∀ a, a ≠ 0 → ∀ k i, 0 ≤ z a k i)
    (hinit : ∀ a, a ≠ 0 → ∀ i, z a 0 i ≤ initialEnvelope i)
    (hstep : ∀ a, a ≠ 0 → ∀ k i, z a (k+1) i ≤ step (z a k) i)
    (htv : ∀ a, a ≠ 0 → ∀ k,
      tv (physicalDifferenceLaw (4+4*k) a) (uniformExcept 0) ≤
        (1/2^17 : ℝ) * score (z a k))
    (k r : ℕ) (hr : 4+4*k ≤ r)
    (first : R → State) (choose : R → State → State) :
    tv (independentView weight (fun t =>
        retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) (first t) (choose t)))
      (independentView weight (fun t =>
        adaptiveDifferenceView randomPermutationDifference (fun y => choose t y-first t))) <
      decimalBound k := by
  apply lt_of_le_of_lt (physical_private_view_tv_le weight hw hs r (rationalBound k)
    (le_of_lt (mul_pos initialCoefficient_pos (pow_pos blockRate_pos k))) ?_ first choose)
    (rational_lt_decimal k)
  intro a ha
  exact (difference_of_profiles z hz hinit hstep htv k r hr a ha).le

end
end AESPaper.PhysicalInterface
