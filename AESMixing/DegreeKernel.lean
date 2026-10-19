import AESMixing.ConstraintExpansion
import Mathlib.SetTheory.Cardinal.Finite

/-! The degree-j matrix is the sum of the mutually orthogonal coordinate
projections. Its Gram entries therefore have the same constraint expansion. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem sum_family_inner {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (f : V → A → ℝ) (g : V → B → ℝ) :
    (∑ v, (∑ a, f v a) * (∑ b, g v b)) = ∑ a, ∑ b, ∑ v, f v a * g v b := by
  simpa only [action, mul_one, one_mul] using
    kernel_bilinear f g (fun _ => 1) (fun _ => 1)

def degreeKernel {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (j : Fin 5) (x y : Fin 4 → V) : ℝ :=
  ∑ a : Fin 4 → Bool, if degreeIndex a = j then productProjection z a x y else 0

theorem degreeKernel_symmetric {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (j : Fin 5) (x y : Fin 4 → V) :
    degreeKernel z j x y = degreeKernel z j y x := by
  unfold degreeKernel
  simp_rw [productProjection_symmetric z _ x y]

theorem degreeKernel_gram {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5) (x y : Fin 4 → V) :
    gram (degreeKernel z j) x y = degreeKernel z j x y := by
  unfold gram degreeKernel
  rw [sum_family_inner]
  have hc (a b : Fin 4 → Bool) :
      (∑ v, (if degreeIndex a = j then productProjection z a v x else 0) *
        (if degreeIndex b = j then productProjection z b v y else 0)) =
      if a = b then (if degreeIndex a = j then productProjection z a x y else 0) else 0 := by
    by_cases ha : degreeIndex a = j
    · by_cases hb : degreeIndex b = j
      · simp only [ha, hb, if_true]
        simp_rw [productProjection_symmetric z a _ x]
        change kernelCompose (productProjection z a) (productProjection z b) x y = _
        rw [productProjection_compose z hn]
        by_cases hab : a = b <;> simp [hab]
      · by_cases hab : a = b
        · subst b
          exact (hb ha).elim
        · simp [hb, hab]
    · simp [ha]
  simp_rw [hc]
  simp

theorem degreeKernel_compose {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5) :
    kernelCompose (degreeKernel z j) (degreeKernel z j) = degreeKernel z j := by
  funext x y
  unfold kernelCompose
  simp_rw [degreeKernel_symmetric z j x]
  exact (degreeKernel_gram z hn j x y).trans (degreeKernel_symmetric z j x y)

theorem degreeKernel_action {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    action (degreeKernel z j) f = degreeComponent z j f := by
  funext x
  unfold action degreeKernel degreeComponent groupedFamily
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degreeIndex a = j <;> simp [ha, action]

theorem degree_response_constraint_count {V A B : Type*}
    [Fintype V] [Zero V] [DecidableEq V] [Fintype A] [Fintype B]
    (hn : 1 < Fintype.card V) (j : Fin 5)
    (L : A → (Fin 4 → V)) (R : B → (Fin 4 → V)) :
    (∑ y, responseColumn (degreeKernel 0 j) L y *
      responseColumn (degreeKernel 0 j) R y) =
      ∑ a : Fin 4 → Bool, if degreeIndex a = j then
        ∑ m : Fin 4 → Fin 5, (∏ i, atomCoefficient (Fintype.card V) (a i) (m i)) *
          Fintype.card {x : A × B // ∀ i,
            atomCondition (m i) (L x.1 i) (R x.2 i)} else 0 := by
  rw [responseColumn_gram (degreeKernel 0 j) (degreeKernel_symmetric 0 j)
    (degreeKernel_compose 0 hn j)]
  rw [← Fintype.sum_prod_type (fun x : A × B => degreeKernel 0 j (L x.1) (R x.2))]
  simp only [degreeKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degreeIndex a = j
  · simp only [ha, if_true]
    simpa only [← Nat.card_eq_fintype_card] using
      projection_constraint_count hn a (fun x : A × B => L x.1)
        (fun x : A × B => R x.2)
  · simp [ha]

end AESMixing
