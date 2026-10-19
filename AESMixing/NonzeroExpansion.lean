import AESMixing.IncidenceKernel
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact inclusion-exclusion for the unmarked nonzero coordinates.
This algebraic identity applies before any norm estimate. It preserves all
joint dependencies among coordinates of the MDS graph. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
attribute [local instance] Classical.propDecidable

theorem finset_indicator_product {J : Type*} [DecidableEq J]
    (s : Finset J) (p : J → Prop) [DecidablePred p] :
    (∏ j ∈ s, if p j then (1 : ℝ) else 0) =
      if ∀ j ∈ s, p j then 1 else 0 := by
  classical
  by_cases h : ∀ j ∈ s, p j
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    exact if_pos (h j hj)
  · rw [if_neg h]
    push Not at h
    obtain ⟨j,hj,hp⟩ := h
    exact Finset.prod_eq_zero hj (if_neg hp)

theorem nonzero_indicator_expansion {J : Type*} [DecidableEq J]
    (s : Finset J) (p : J → Prop) [DecidablePred p] :
    (if ∀ j ∈ s, ¬p j then (1 : ℝ) else 0) =
      ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
        if ∀ j ∈ t, p j then 1 else 0 := by
  have hp (j : J) : (if ¬p j then (1 : ℝ) else 0) =
      1 - (if p j then 1 else 0) := by
    by_cases h : p j <;> simp [h]
  rw [← finset_indicator_product s (fun j => ¬p j)]
  simp_rw [hp]
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, finset_indicator_product]

theorem nonzero_weighted_expansion {J C : Type*} [DecidableEq J] [Fintype C]
    (s : Finset J) (p : J → C → Prop) [∀ j, DecidablePred (p j)]
    (w : C → ℝ) :
    (∑ c, (if ∀ j ∈ s, ¬p j c then (1 : ℝ) else 0) * w c) =
      ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
        ∑ c, (if ∀ j ∈ t, p j c then (1 : ℝ) else 0) * w c := by
  classical
  simp_rw [nonzero_indicator_expansion s (fun j => p j _), Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

end AESMixing
