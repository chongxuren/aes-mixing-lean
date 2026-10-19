import AESMixing.PairExperiment

/-! Exact finite two-query experiments. Adaptivity is justified by the
uniform first-output identity, not by assuming that fixed-pair TV alone
controls adaptive queries. Concrete AES instantiation remains separate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V K : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V] [Fintype K]

def retainedPairLaw (E : K → V → V) (weight : K → ℝ)
    (x x' : V) (y : V × V) : ℝ :=
  ∑ k, weight k * if E k x = y.1 ∧ E k x' = y.2 then 1 else 0

def retainedAdaptiveLaw (E : K → V → V) (weight : K → ℝ)
    (x : V) (choose : V → V) (y : V × V) : ℝ :=
  ∑ k, weight k * if E k x = y.1 ∧ E k (choose (E k x)) = y.2 then 1 else 0

omit [Fintype V] [AddCommGroup V] in
theorem retained_adaptive_pair_identity (E : K → V → V) (weight : K → ℝ)
    (x : V) (choose : V → V) (y : V × V) :
    retainedAdaptiveLaw E weight x choose y = retainedPairLaw E weight x (choose y.1) y := by
  unfold retainedAdaptiveLaw retainedPairLaw
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : E k x = y.1 <;> simp [h]

omit [Fintype K] in
def adaptiveDifferenceView (p : V → V → ℝ) (choose : V → V) (y : V × V) : ℝ :=
  p (choose y.1) (y.2 - y.1) / Fintype.card V

omit [Fintype K] [DecidableEq V] in
theorem tv_adaptive_difference_le (p q : V → V → ℝ) (choose : V → V) (eps : ℝ)
    (h : ∀ a, tv (p a) (q a) ≤ eps) :
    tv (adaptiveDifferenceView p choose) (adaptiveDifferenceView q choose) ≤ eps := by
  change tv (uniformRows (fun y => p (choose y)) ∘ pairCoordinates)
    (uniformRows (fun y => q (choose y)) ∘ pairCoordinates) ≤ eps
  rw [tv_relabel]
  exact tv_uniformRows_le _ _ eps (fun y => h (choose y))

theorem retained_adaptive_difference_identity (E : K → V → V) (weight : K → ℝ)
    (p : V → V → ℝ)
    (h : ∀ x x' y, retainedPairLaw E weight x x' y =
      p (x'-x) (y.2-y.1) / Fintype.card V)
    (x : V) (choose : V → V) :
    retainedAdaptiveLaw E weight x choose = adaptiveDifferenceView p (fun y => choose y-x) := by
  funext y
  rw [retained_adaptive_pair_identity, h]
  rfl

section IndependentInformation
variable {R X : Type*} [Fintype R] [Fintype X]

def independentView (weight : R → ℝ) (p : R → X → ℝ) (view : R × X) : ℝ :=
  weight view.1 * p view.1 view.2

theorem tv_independent_view (weight : R → ℝ) (hw : ∀ r, 0 ≤ weight r)
    (p q : R → X → ℝ) :
    tv (independentView weight p) (independentView weight q) =
      ∑ r, weight r * tv (p r) (q r) := by
  unfold tv independentView
  simp only [Fintype.sum_prod_type, ← mul_sub, abs_mul, abs_of_nonneg (hw _),
    ← Finset.mul_sum, Finset.sum_div, mul_div_assoc]

theorem tv_independent_view_le (weight : R → ℝ) (hw : ∀ r, 0 ≤ weight r)
    (hs : (∑ r, weight r) = 1) (p q : R → X → ℝ) (eps : ℝ)
    (h : ∀ r, tv (p r) (q r) ≤ eps) :
    tv (independentView weight p) (independentView weight q) ≤ eps := by
  rw [tv_independent_view weight hw]
  calc
    (∑ r, weight r * tv (p r) (q r)) ≤ ∑ r, weight r * eps :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (h r) (hw r))
    _ = eps := by rw [← Finset.sum_mul, hs, one_mul]

end IndependentInformation
end AESMixing
