import AESMixing.Centering

/-! The word activity projection and its orthogonal residual, explicitly as
functions. These are counting-measure projections, not probability norms. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

def nonzeroMean (zero : V) (f : V → ℝ) : ℝ :=
  ((∑ x, f x) - f zero) / (Fintype.card V - 1 : ℝ)

def wordAverage (zero : V) (f : V → ℝ) (x : V) : ℝ :=
  if x = zero then f zero else nonzeroMean zero f

def wordResidual (zero : V) (f : V → ℝ) : V → ℝ := f - wordAverage zero f

theorem wordAverage_at_zero (zero : V) (f : V → ℝ) :
    wordAverage zero f zero = f zero := by simp [wordAverage]

theorem wordResidual_at_zero (zero : V) (f : V → ℝ) :
    wordResidual zero f zero = 0 := by simp [wordResidual, wordAverage]

theorem wordAverage_sum (zero : V) (f : V → ℝ) (hn : 1 < Fintype.card V) :
    (∑ x, wordAverage zero f x) = ∑ x, f x := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (Fintype.card V - 1 : ℝ) ≠ 0 := by linarith
  have hp (x : V) : wordAverage zero f x = nonzeroMean zero f +
      if x = zero then f zero - nonzeroMean zero f else 0 := by
    by_cases hx : x = zero <;> simp [wordAverage, hx]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold nonzeroMean
  field_simp
  ring

theorem wordResidual_sum (zero : V) (f : V → ℝ) (hn : 1 < Fintype.card V) :
    (∑ x, wordResidual zero f x) = 0 := by
  simp only [wordResidual, Pi.sub_apply, Finset.sum_sub_distrib, wordAverage_sum zero f hn,
    sub_self]

theorem wordAverage_idempotent (zero : V) (f : V → ℝ) (hn : 1 < Fintype.card V) :
    wordAverage zero (wordAverage zero f) = wordAverage zero f := by
  funext x
  have hm : nonzeroMean zero (wordAverage zero f) = nonzeroMean zero f := by
    simp only [nonzeroMean, wordAverage_sum zero f hn, wordAverage_at_zero]
  change (if x = zero then wordAverage zero f zero else
    nonzeroMean zero (wordAverage zero f)) = wordAverage zero f x
  rw [wordAverage_at_zero, hm]
  rfl

theorem activity_residual_orthogonal (zero : V) (f g : V → ℝ)
    (hn : 1 < Fintype.card V) :
    (∑ x, wordAverage zero f x * wordResidual zero g x) = 0 := by
  have hp (x : V) : wordAverage zero f x * wordResidual zero g x =
      nonzeroMean zero f * wordResidual zero g x := by
    by_cases hx : x = zero
    · subst x; simp [wordResidual_at_zero]
    · simp [wordAverage, hx]
  simp_rw [hp]
  rw [← Finset.mul_sum, wordResidual_sum zero g hn, mul_zero]

theorem activity_residual_pythagoras (zero : V) (f : V → ℝ)
    (hn : 1 < Fintype.card V) :
    (∑ x, f x ^ 2) =
      (∑ x, wordAverage zero f x ^ 2) + ∑ x, wordResidual zero f x ^ 2 := by
  have hp (x : V) : f x ^ 2 = wordAverage zero f x ^ 2 + wordResidual zero f x ^ 2 +
      2 * (wordAverage zero f x * wordResidual zero f x) := by
    simp only [wordResidual, Pi.sub_apply]
    ring
  simp_rw [hp, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, activity_residual_orthogonal zero f f hn]
  ring

end AESMixing
