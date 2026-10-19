import AESMixing.ProjectionGram
import Mathlib.Data.Fintype.BigOperators

/-! The five linear-constraint atoms in the activity Gram computation.
This is an exact expansion of the concrete coordinate projections, not a
postulated table. The final counts will be supplied by field certificates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def atomCondition {V : Type*} [Zero V] (m : Fin 5) (x y : V) : Prop :=
  match m.val with
  | 0 => True
  | 1 => x = 0
  | 2 => y = 0
  | 3 => x = 0 ∧ y = 0
  | _ => x = y

instance {V : Type*} [Zero V] [DecidableEq V] (m : Fin 5) (x y : V) :
    Decidable (atomCondition m x y) := by
  unfold atomCondition
  split <;> infer_instance

def atomCoefficient (q : ℝ) (b : Bool) (m : Fin 5) : ℝ :=
  if b then ![-1/(q-1), 1/(q-1), 1/(q-1), -q/(q-1), 1] m
  else ![1/(q-1), -1/(q-1), -1/(q-1), q/(q-1), 0] m

theorem degreePiece_atoms {V : Type*} [Fintype V] [Zero V] [DecidableEq V]
    (hn : 1 < Fintype.card V) (b : Bool) (x y : V) :
    degreePiece 0 b x y = ∑ m : Fin 5,
      atomCoefficient (Fintype.card V) b m * if atomCondition m x y then 1 else 0 := by
  have hq : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have hh : 1 < (Fintype.card V : ℝ) := by exact_mod_cast hn
    linarith
  cases b <;> by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    by_cases hxy : x = y <;>
    simp [degreePiece, residualProjection, identityKernel, activityMatrix,
      atomCoefficient, atomCondition, Fin.sum_univ_succ, hx, hy, hxy] <;>
    field_simp [hq] <;> ring

theorem product_indicator {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] :
    (∏ i, if p i then (1 : ℝ) else 0) = if ∀ i, p i then 1 else 0 := by
  classical
  by_cases h : ∀ i, p i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem productProjection_atoms {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [Zero V] [DecidableEq V] (hn : 1 < Fintype.card V)
    (a : I → Bool) (x y : I → V) :
    productProjection 0 a x y = ∑ m : I → Fin 5,
      (∏ i, atomCoefficient (Fintype.card V) (a i) (m i)) *
      if ∀ i, atomCondition (m i) (x i) (y i) then 1 else 0 := by
  unfold productProjection
  simp_rw [degreePiece_atoms hn]
  rw [Fintype.prod_sum (fun i m => atomCoefficient (Fintype.card V) (a i) m *
    if atomCondition m (x i) (y i) then 1 else 0)]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.prod_mul_distrib, product_indicator]

theorem indicator_sum_card {X : Type*} [Fintype X]
    (p : X → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℝ) else 0) = Fintype.card {x // p x} := by
  simp [Fintype.card_subtype]

theorem projection_constraint_count {I V X : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Zero V] [DecidableEq V] [Fintype X]
    (hn : 1 < Fintype.card V) (a : I → Bool) (L R : X → (I → V)) :
    (∑ x, productProjection 0 a (L x) (R x)) =
      ∑ m : I → Fin 5, (∏ i, atomCoefficient (Fintype.card V) (a i) (m i)) *
        Fintype.card {x // ∀ i, atomCondition (m i) (L x i) (R x i)} := by
  simp_rw [productProjection_atoms hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.mul_sum, indicator_sum_card]

/-- Exact Gram entry of two actual projected graph columns. -/
theorem responseColumn_constraint_count {I V A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Zero V] [DecidableEq V]
    [Fintype A] [Fintype B]
    (hn : 1 < Fintype.card V) (a : I → Bool)
    (L : A → (I → V)) (R : B → (I → V)) :
    (∑ y, responseColumn (productProjection 0 a) L y *
      responseColumn (productProjection 0 a) R y) =
      ∑ m : I → Fin 5, (∏ i, atomCoefficient (Fintype.card V) (a i) (m i)) *
        Fintype.card {x : A × B // ∀ i,
          atomCondition (m i) (L x.1 i) (R x.2 i)} := by
  rw [responseColumn_gram (productProjection 0 a) (productProjection_symmetric 0 a)
    (by rw [productProjection_compose 0 hn, if_pos rfl])]
  simpa only [Fintype.sum_prod_type] using
    projection_constraint_count hn a (fun x : A × B => L x.1)
      (fun x : A × B => R x.2)

end AESMixing
