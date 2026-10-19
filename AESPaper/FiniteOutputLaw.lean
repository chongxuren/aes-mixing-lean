import AESPaper.PhysicalView
import Mathlib.Tactic.SplitIfs

/-!
# Finite deterministic output laws
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AESPaper.FiniteOutputLaw
open AESMixing

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq Y] [DecidableEq Z]

def pushLaw (g : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if g x = y then p x else 0

theorem pushLaw_eq_action (g : X → Y) (p : X → ℝ) :
    pushLaw g p = action (fun y x => if g x = y then 1 else 0) p := by
  funext y
  simp only [pushLaw, action, ite_mul, one_mul, zero_mul]

/-- Deterministic postprocessing never increases half-l1 total variation. -/
theorem tv_pushLaw_le (g : X → Y) (p q : X → ℝ) :
    tv (pushLaw g p) (pushLaw g q) ≤ tv p q := by
  rw [pushLaw_eq_action, pushLaw_eq_action]
  apply tv_action_le
  · intro y x
    split_ifs <;> norm_num
  · intro x
    simp

theorem pushLaw_nonnegative (g : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (y : Y) : 0 ≤ pushLaw g p y := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hp x
  · exact le_rfl

theorem pushLaw_total (g : X → Y) (p : X → ℝ) :
    (∑ y, pushLaw g p y) = ∑ x, p x := by
  unfold pushLaw
  rw [Finset.sum_comm]
  simp

/-- Composition holds for arbitrary finite signed input weights. -/
theorem pushLaw_comp (g : X → Y) (h : Y → Z) (p : X → ℝ) :
    pushLaw h (pushLaw g p) = pushLaw (fun x => h (g x)) p := by
  funext z
  unfold pushLaw
  have houter (y : Y) :
      (if h y = z then (∑ x, if g x = y then p x else 0) else 0) =
        ∑ x, if h y = z then (if g x = y then p x else 0) else 0 := by
    by_cases hy : h y = z <;> simp [hy]
  simp_rw [houter]
  rw [Finset.sum_comm]
  have hterm (x : X) (y : Y) :
      (if h y = z then (if g x = y then p x else 0) else 0) =
        (if g x = y then (if h (g x) = z then p x else 0) else 0) := by
    by_cases hxy : g x = y
    · subst y
      simp
    · simp [hxy]
  simp_rw [hterm]
  simp

theorem pushLaw_point [DecidableEq X] (g : X → Y) (x : X) :
    pushLaw g (differencePoint x) = differencePoint (g x) := by
  funext y
  unfold pushLaw differencePoint
  have hterm (z : X) :
      (if g z = y then (if x = z then (1 : ℝ) else 0) else 0) =
        (if x = z then (if g x = y then 1 else 0) else 0) := by
    by_cases hx : x = z
    · subst z
      simp
    · simp [hx]
  simp_rw [hterm]
  simp

theorem pushLaw_const (p : X → ℝ) (a y : Y) :
    pushLaw (fun _ : X => a) p y = if a = y then (∑ x, p x) else 0 := by
  by_cases h : a = y <;> simp [pushLaw, h]

/-- A seed is retained in the private view before the deterministic decoder.
Its distribution may encode arbitrary finite independent prior information. -/
theorem pushLaw_independent {R : Type*} [Fintype R]
    (weight : R → ℝ) (p : R → X → ℝ) (decode : R × X → Y) (y : Y) :
    pushLaw decode (independentView weight p) y =
      ∑ t, weight t * pushLaw (fun x => decode (t, x)) (p t) y := by
  simp only [pushLaw, independentView, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : decode (t, x) = y <;> simp [h]

end AESPaper.FiniteOutputLaw
