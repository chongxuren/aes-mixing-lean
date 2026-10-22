import AESRound.Imports

/-!
# Positive second-order profile comparisons

This file contains no AES-specific assumptions or target error bounds.  It
separates the finite-dimensional comparison argument from the analytic theorem
that an actual cipher's component norms satisfy that comparison.

The finite prefix may contain outward-rounded rational bounds.  After two
consecutive actual states enter an invariant box, the unrounded recurrence for
the actual states proves every later bound.  No infinite rounding recurrence is
silently substituted for that argument.
-/

noncomputable section

namespace AESRound

abbrev Profile (ι : Type*) := ι → ℝ

def EntrywiseNonnegative {ι : Type*} (M : ι → ι → ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

def matVec {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (x : Profile ι) : Profile ι :=
  fun i => ∑ j, M i j * x j

theorem matVec_mono {ι : Type*} [Fintype ι] {M : ι → ι → ℝ}
    (hM : EntrywiseNonnegative M) : Monotone (matVec M) := by
  intro x y hxy i
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hM i j)

theorem matVec_nonneg {ι : Type*} [Fintype ι] {M : ι → ι → ℝ}
    (hM : EntrywiseNonnegative M) {x : Profile ι}
    (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ matVec M x i := by
  intro i
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hM i j) (hx j)

theorem matVec_scale {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (α : ℝ) (x : Profile ι) :
    matVec M (fun i => α * x i) = fun i => α * matVec M x i := by
  funext i
  dsimp [matVec]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The one-step and memory bounds apply to the same actual component, so their
coordinatewise minimum is again an upper bound. -/
def comparisonStep {ι : Type*} [Fintype ι]
    (L H J : ι → ι → ℝ) (current previous : Profile ι) : Profile ι :=
  fun i => min (matVec L current i)
    (matVec H current i + matVec J previous i)

theorem comparisonStep_mono {ι : Type*} [Fintype ι]
    {L H J : ι → ι → ℝ}
    (hL : EntrywiseNonnegative L) (hH : EntrywiseNonnegative H)
    (hJ : EntrywiseNonnegative J)
    {current₁ current₂ previous₁ previous₂ : Profile ι}
    (hcurrent : current₁ ≤ current₂) (hprevious : previous₁ ≤ previous₂) :
    comparisonStep L H J current₁ previous₁ ≤
      comparisonStep L H J current₂ previous₂ := by
  intro i
  apply min_le_min
  · exact (matVec_mono hL hcurrent) i
  · exact add_le_add ((matVec_mono hH hcurrent) i)
      ((matVec_mono hJ hprevious) i)

/-- A finite certificate needs only outward inequalities, not equality with a
particular rounding algorithm. -/
theorem finite_prefix_comparison {ι : Type*} [Fintype ι]
    {L H J : ι → ι → ℝ}
    (hL : EntrywiseNonnegative L) (hH : EntrywiseNonnegative H)
    (hJ : EntrywiseNonnegative J)
    {actual certificate : ℕ → Profile ι} {last : ℕ}
    (hzero : actual 0 ≤ certificate 0)
    (hone : actual 1 ≤ certificate 1)
    (hactual : ∀ n, actual (n + 2) ≤
      comparisonStep L H J (actual (n + 1)) (actual n))
    (hcertificate : ∀ n, n + 2 ≤ last →
      comparisonStep L H J (certificate (n + 1)) (certificate n) ≤
        certificate (n + 2)) :
    ∀ n, n ≤ last → actual n ≤ certificate n := by
  apply Nat.twoStepInduction
  · intro _
    exact hzero
  · intro _
    exact hone
  · intro n hn hn₁ hn₂
    exact le_trans (hactual n)
      (le_trans
        (comparisonStep_mono hL hH hJ (hn₁ (by omega)) (hn (by omega)))
        (hcertificate n hn₂))

/-- A second-order positive recurrence remains in a box once two consecutive
actual states lie in that box.  The one-step matrix L need not be positive for
this theorem because only the memory branch is used after entry. -/
theorem invariant_box_from_two_states {ι : Type*} [Fintype ι]
    {L H J : ι → ι → ℝ}
    (hH : EntrywiseNonnegative H) (hJ : EntrywiseNonnegative J)
    {actual : ℕ → Profile ι} {bound : Profile ι} {start : ℕ}
    (hactual : ∀ n, actual (n + 2) ≤
      comparisonStep L H J (actual (n + 1)) (actual n))
    (hinvariant : ∀ i, matVec H bound i + matVec J bound i ≤ bound i)
    (hstart : actual start ≤ bound)
    (hnext : actual (start + 1) ≤ bound) :
    ∀ n, start ≤ n → actual n ≤ bound := by
  have hshift : ∀ t, actual (start + t) ≤ bound := by
    apply Nat.twoStepInduction
    · simpa using hstart
    · simpa using hnext
    · intro t ht ht₁ i
      calc
        actual (start + (t + 2)) i ≤
            comparisonStep L H J (actual (start + (t + 1)))
              (actual (start + t)) i := by
          simpa only [Nat.add_assoc] using (hactual (start + t)) i
        _ ≤ matVec H (actual (start + (t + 1))) i +
              matVec J (actual (start + t)) i := min_le_right _ _
        _ ≤ matVec H bound i + matVec J bound i :=
          add_le_add ((matVec_mono hH ht₁) i) ((matVec_mono hJ ht) i)
        _ ≤ bound i := hinvariant i
  intro n hn
  have hindex : start + (n - start) = n := by omega
  simpa only [hindex] using hshift (n - start)

/-- A positive-vector inequality for H+J gives an invariant scaled cone bound.
Nonnegativity of d is not required for this implication; concrete certificates
may establish positivity separately to interpret coordinate ratios. -/
theorem invariant_cone_from_two_states {ι : Type*} [Fintype ι]
    {L H J : ι → ι → ℝ}
    (hH : EntrywiseNonnegative H) (hJ : EntrywiseNonnegative J)
    {actual : ℕ → Profile ι} {d : Profile ι} {α : ℝ} {start : ℕ}
    (hα : 0 ≤ α)
    (hactual : ∀ n, actual (n + 2) ≤
      comparisonStep L H J (actual (n + 1)) (actual n))
    (hcone : ∀ i, matVec H d i + matVec J d i ≤ d i)
    (hstart : actual start ≤ fun i => α * d i)
    (hnext : actual (start + 1) ≤ fun i => α * d i) :
    ∀ n, start ≤ n → actual n ≤ fun i => α * d i := by
  apply invariant_box_from_two_states hH hJ hactual ?_ hstart hnext
  intro i
  rw [matVec_scale, matVec_scale]
  calc
    α * matVec H d i + α * matVec J d i =
        α * (matVec H d i + matVec J d i) := by ring
    _ ≤ α * d i := mul_le_mul_of_nonneg_left (hcone i) hα

/-- A checked finite prefix and two terminal cone comparisons supply the base
states of the all-round theorem.  No output error estimate is assumed. -/
theorem cone_from_finite_certificate {ι : Type*} [Fintype ι]
    {L H J : ι → ι → ℝ}
    (hL : EntrywiseNonnegative L) (hH : EntrywiseNonnegative H)
    (hJ : EntrywiseNonnegative J)
    {actual certificate : ℕ → Profile ι} {d : Profile ι}
    {α : ℝ} {start : ℕ}
    (hα : 0 ≤ α)
    (hzero : actual 0 ≤ certificate 0)
    (hone : actual 1 ≤ certificate 1)
    (hactual : ∀ n, actual (n + 2) ≤
      comparisonStep L H J (actual (n + 1)) (actual n))
    (hcertificate : ∀ n, n + 2 ≤ start + 1 →
      comparisonStep L H J (certificate (n + 1)) (certificate n) ≤
        certificate (n + 2))
    (hcone : ∀ i, matVec H d i + matVec J d i ≤ d i)
    (hstart : certificate start ≤ fun i => α * d i)
    (hnext : certificate (start + 1) ≤ fun i => α * d i) :
    ∀ n, start ≤ n → actual n ≤ fun i => α * d i := by
  have hprefix := finite_prefix_comparison hL hH hJ hzero hone hactual
    hcertificate
  apply invariant_cone_from_two_states hH hJ hα hactual hcone
  · exact le_trans (hprefix start (by omega)) hstart
  · exact le_trans (hprefix (start + 1) le_rfl) hnext

end AESRound
