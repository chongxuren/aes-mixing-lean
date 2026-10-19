import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted diagonal dominance and nonnegative finite quadratics

This generic real-algebra result has no numerical or AES premises. A positive
diagonal change of coordinates reduces weighted row domination to ordinary
symmetric diagonal dominance. The latter is proved by a sum of pairwise
square inequalities. Numerical row bounds and actual matrix identification
belong to separate callers.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WeightedDiagonalDominance

variable {I : Type*} [Fintype I] [DecidableEq I]

def qForm (M : I → I → ℝ) (x : I → ℝ) : ℝ :=
  ∑ i : I, ∑ j : I, x i*x j*M i j

def offDiagonal (M : I → I → ℝ) (i j : I) : ℝ :=
  if i = j then 0 else M i j

def rowAbs (M : I → I → ℝ) (i : I) : ℝ :=
  ∑ j : I, if i = j then 0 else |M i j|

private theorem abs_offDiagonal (M : I → I → ℝ) (i j : I) :
    |offDiagonal M i j| = if i = j then 0 else |M i j| := by
  by_cases h : i = j <;> simp [offDiagonal, h]

private theorem offDiagonal_symmetric (M : I → I → ℝ)
    (hM : ∀ i j, M i j = M j i) (i j : I) :
    offDiagonal M i j = offDiagonal M j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [offDiagonal, h, Ne.symm h, hM i j]

/-- Separate the diagonal exactly, without any sign assumptions. -/
theorem qForm_split (M : I → I → ℝ) (x : I → ℝ) :
    qForm M x = (∑ i : I, M i i*(x i)^2) + qForm (offDiagonal M) x := by
  have hp (i j : I) : x i*x j*M i j =
      (if j = i then M i i*(x i)^2 else 0) + x i*x j*offDiagonal M i j := by
    by_cases h : j = i
    · subst j
      simp [offDiagonal]
      ring
    · simp [offDiagonal, h, Ne.symm h]
  unfold qForm
  calc
    _ = ∑ i : I, ∑ j : I,
        ((if j = i then M i i*(x i)^2 else 0) +
          x i*x j*offDiagonal M i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hp i j
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem pair_nonneg (a x y : ℝ) :
    0 ≤ |a| * (x^2+y^2) + 2*(x*y*a) := by
  have hplus : 0 ≤ |a|+a := by linarith [neg_abs_le a]
  have hminus : 0 ≤ |a|-a := sub_nonneg.mpr (le_abs_self a)
  have hp := mul_nonneg hplus (sq_nonneg (x+y))
  have hm := mul_nonneg hminus (sq_nonneg (x-y))
  nlinarith only [hp, hm]

/-- Ordinary symmetric diagonal dominance gives a nonnegative quadratic.
The diagonal itself is not replaced by its absolute value. -/
theorem quadratic_nonneg_of_diagonal_dominance
    (M : I → I → ℝ) (hM : ∀ i j, M i j = M j i)
    (hdom : ∀ i, rowAbs M i ≤ M i i) (x : I → ℝ) :
    0 ≤ qForm M x := by
  have hleft :
      (∑ i : I, ∑ j : I, |offDiagonal M i j| * (x i)^2) =
        ∑ i : I, rowAbs M i*(x i)^2 := by
    symm
    unfold rowAbs
    simp_rw [Finset.sum_mul, abs_offDiagonal]
  have hright :
      (∑ i : I, ∑ j : I, |offDiagonal M i j| * (x j)^2) =
        ∑ i : I, rowAbs M i*(x i)^2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i : I, ∑ j : I, |offDiagonal M i j| * (x i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [offDiagonal_symmetric M hM j i]
      _ = _ := hleft
  have hpair : 0 ≤ ∑ i : I, ∑ j : I,
      (|offDiagonal M i j| * ((x i)^2+(x j)^2) +
        2*(x i*x j*offDiagonal M i j)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact pair_nonneg _ _ _
  have hpair_eq :
      (∑ i : I, ∑ j : I,
        (|offDiagonal M i j| * ((x i)^2+(x j)^2) +
          2*(x i*x j*offDiagonal M i j))) =
      2*(∑ i : I, rowAbs M i*(x i)^2) + 2*qForm (offDiagonal M) x := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hleft, hright]
    unfold qForm
    ring
  rw [hpair_eq] at hpair
  have hdiag : (∑ i : I, rowAbs M i*(x i)^2) ≤
      ∑ i : I, M i i*(x i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg (x i))
  rw [qForm_split]
  linarith

/-- Weighted symmetric diagonal dominance. Strict positivity permits the
coordinate division; the row domination inequality itself may be non-strict. -/
theorem weighted_diagonal_nonneg
    (M : I → I → ℝ) (w : I → ℝ)
    (hM : ∀ i j, M i j = M j i) (hw : ∀ i, 0 < w i)
    (hdom : ∀ i, (∑ j : I, if i = j then 0 else |M i j| * w j) ≤ M i i*w i)
    (x : I → ℝ) :
    0 ≤ ∑ i : I, ∑ j : I, x i*x j*M i j := by
  let N : I → I → ℝ := fun i j => M i j*w i*w j
  let y : I → ℝ := fun i => x i/w i
  have hN : ∀ i j, N i j = N j i := by
    intro i j
    dsimp [N]
    rw [hM i j]
    ring
  have hNdom : ∀ i, rowAbs N i ≤ N i i := by
    intro i
    calc
      rowAbs N i = (∑ j : I, if i = j then 0 else |M i j| * w j)*w i := by
        unfold rowAbs
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · simp [h]
        · simp only [h, if_false, N, abs_mul, abs_of_pos (hw i), abs_of_pos (hw j)]
          ring
      _ ≤ (M i i*w i)*w i := mul_le_mul_of_nonneg_right (hdom i) (le_of_lt (hw i))
      _ = N i i := by rfl
  have hq := quadratic_nonneg_of_diagonal_dominance N hN hNdom y
  have heq : qForm N y = qForm M x := by
    unfold qForm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [N, y]
    field_simp [ne_of_gt (hw i), ne_of_gt (hw j)]
  rw [heq] at hq
  exact hq

end AESConcrete.WeightedDiagonalDominance
