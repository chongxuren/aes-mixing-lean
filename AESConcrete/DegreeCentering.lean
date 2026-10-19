import AESMixing.ResidualCoordinates
import AESMixing.DegreeKernel

/-!
# Positive degree and global uniform centering

A positive degree marks at least one residual coordinate. Its output
therefore vanishes at the distinguished constant state and has total mass
zero, even for arbitrary joint input functions. The global uniform-nonzero
kernel annihilates each such degree projection on either side.

The alphabet is generic: specializing it to `AES.Word` counts residual
32-bit words. This module assumes no quantitative bound and makes no claim
about the fourteen exact-support refinements. Only constructive identities
are proved; no attacks or manuscript edits are in scope.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DegreeCentering
open AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The state whose four coordinates are the distinguished alphabet value. -/
def distinguishedState (z : V) : Fin 4 → V := fun _ => z

/-- Every positive-degree pattern marks a residual coordinate. -/
theorem positive_degree_has_marked (a : Fin 4 → Bool)
    (ha : degreeIndex a ≠ 0) : ∃ k, a k = true := by
  by_contra h
  push Not at h
  apply ha
  apply (degreeIndex_zero_iff a).mpr
  exact funext (fun k => Bool.eq_false_iff.mpr (h k))

/-- Positive-degree outputs are globally centered, without assumptions on
the input function. Degree is relative to the chosen alphabet. -/
theorem positive_degree_centered (z : V) (hn : 1 < Fintype.card V)
    (j : Fin 5) (hj : j ≠ 0) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j f (distinguishedState z) = 0 ∧
      (∑ x, degreeComponent z j f x) = 0 := by
  have hp (a : Fin 4 → Bool) (ha : degreeIndex a = j) :
      action (productProjection z a) f (distinguishedState z) = 0 ∧
        (∑ x, action (productProjection z a) f x) = 0 := by
    obtain ⟨k, hk⟩ := positive_degree_has_marked a (by simpa only [ha] using hj)
    exact ⟨productProjection_marked_zero z a k hk f _ rfl,
      productProjection_marked_sum z hn a k hk f⟩
  unfold degreeComponent groupedFamily
  constructor
  · apply Finset.sum_eq_zero
    intro a _
    by_cases ha : degreeIndex a = j
    · simp only [ha, if_true]
      exact (hp a ha).1
    · simp only [ha, if_false]
  · rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : degreeIndex a = j
    · simp only [ha, if_true]
      exact (hp a ha).2
    · simp only [ha, if_false, Finset.sum_const_zero]

theorem degreeComponent_at_distinguishedState (z : V)
    (hn : 1 < Fintype.card V) (j : Fin 5) (hj : j ≠ 0)
    (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j f (distinguishedState z) = 0 :=
  (positive_degree_centered z hn j hj f).1

theorem degreeComponent_sum_zero (z : V)
    (hn : 1 < Fintype.card V) (j : Fin 5) (hj : j ≠ 0)
    (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x) = 0 :=
  (positive_degree_centered z hn j hj f).2

/-- Global uniform-nonzero kernel: the distinguished state has zero row
and column, and all other entries equal `1/(card(V^4)-1)`. This is not
the local activity projection, which preserves the distinguished state. -/
def globalUniformKernel (z : V) (y x : Fin 4 → V) : ℝ :=
  if y = distinguishedState z then 0 else
    if x = distinguishedState z then 0 else
      1 / (Fintype.card (Fin 4 → V) - 1 : ℝ)

theorem globalUniformKernel_symmetric (z : V) (x y : Fin 4 → V) :
    globalUniformKernel z x y = globalUniformKernel z y x := by
  by_cases hx : x = distinguishedState z <;>
    by_cases hy : y = distinguishedState z <;>
    simp [globalUniformKernel, hx, hy]

/-- Acting by the global kernel keeps only the total mass outside the
distinguished state and distributes it uniformly outside that state. -/
theorem globalUniformKernel_action (z : V) (f : (Fin 4 → V) → ℝ)
    (y : Fin 4 → V) :
    action (globalUniformKernel z) f y =
      if y = distinguishedState z then 0 else
        ((∑ x, f x) - f (distinguishedState z)) /
          (Fintype.card (Fin 4 → V) - 1 : ℝ) := by
  by_cases hy : y = distinguishedState z
  · simp [action, globalUniformKernel, hy]
  · have hp (x : Fin 4 → V) : globalUniformKernel z y x * f x =
        (f x - if x = distinguishedState z then f (distinguishedState z) else 0) /
          (Fintype.card (Fin 4 → V) - 1 : ℝ) := by
      by_cases hx : x = distinguishedState z
      · subst x
        simp [globalUniformKernel, hy]
      · simp [globalUniformKernel, hy, hx, div_eq_mul_inv, mul_comm]
    simp only [action, hp, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp [hy]

theorem globalUniformKernel_action_eq_zero (z : V)
    (f : (Fin 4 → V) → ℝ) (hz : f (distinguishedState z) = 0)
    (hs : (∑ x, f x) = 0) : action (globalUniformKernel z) f = 0 := by
  funext y
  rw [globalUniformKernel_action]
  simp [hz, hs]

/-- The global uniform-nonzero term vanishes on positive-degree inputs. -/
theorem globalUniformKernel_compose_degreeKernel (z : V)
    (hn : 1 < Fintype.card V) (j : Fin 5) (hj : j ≠ 0) :
    kernelCompose (globalUniformKernel z) (degreeKernel z j) = 0 := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, degreeKernel_action,
    globalUniformKernel_action_eq_zero z _
      (degreeComponent_at_distinguishedState z hn j hj f)
      (degreeComponent_sum_zero z hn j hj f)]
  funext x
  simp [action]

/-- Symmetry gives the matching annihilation on the output leg. -/
theorem degreeKernel_compose_globalUniformKernel (z : V)
    (hn : 1 < Fintype.card V) (j : Fin 5) (hj : j ≠ 0) :
    kernelCompose (degreeKernel z j) (globalUniformKernel z) = 0 := by
  funext y x
  change kernelCompose (degreeKernel z j) (globalUniformKernel z) y x = 0
  calc
    _ = kernelCompose (globalUniformKernel z) (degreeKernel z j) x y := by
      unfold kernelCompose
      apply Finset.sum_congr rfl
      intro a _
      rw [degreeKernel_symmetric z j y a, globalUniformKernel_symmetric z a x]
      exact mul_comm _ _
    _ = 0 := by
      simpa only [Pi.zero_apply] using congrFun
        (congrFun (globalUniformKernel_compose_degreeKernel z hn j hj) x) y

end AESConcrete.DegreeCentering
