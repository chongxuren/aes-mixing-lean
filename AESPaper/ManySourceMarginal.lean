import AESConcrete.RestrictedMarginalEnergy
import AESMixing.LawRelabel

/-!
# Finite pushforward algebra for four independent source labels
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ManySourceMarginal
open AESMixing
open AESConcrete.RestrictedMarginalEnergy (marginal)

theorem marginal_id {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ) :
    marginal (fun x : V => x) f = f := by
  funext y
  simp only [marginal, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem marginal_mass {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (coord : X → Y) (f : X → ℝ) :
    (∑ y, marginal coord f y) = ∑ x, f x := by
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Law weights use the inverse map; the observed coordinates use its forward map. -/
theorem marginal_relabel {X Y : Type*} [Fintype X] [DecidableEq Y]
    (L : Equiv.Perm X) (f : X → ℝ) (coord : X → Y) :
    marginal coord (lawRelabel L f) = marginal (fun x => coord (L x)) f := by
  funext y
  have h := Equiv.sum_comp L (fun x => if coord x = y then f (L.symm x) else 0)
  simpa only [marginal, lawRelabel, L.symm_apply_apply] using h.symm

/-- Independent source labels are kept through both source maps. -/
theorem pair_marginal_eq_convolution {X Z V : Type*}
    [Fintype X] [Fintype Z] [Fintype V] [DecidableEq V] [AddCommGroup V]
    (L : X → V) (R : Z → V) (f : X → ℝ) (g : Z → ℝ) :
    marginal (fun p : X × Z => L p.1 + R p.2) (fun p => f p.1 * g p.2) =
      convolution (marginal L f) (marginal R g) := by
  symm
  funext y
  unfold convolution
  calc
    _ = ∑ u : V, ∑ x : X, ∑ z : Z,
        (if L x = u then f x else 0) * (if R z = y-u then g z else 0) := by
      simp only [marginal]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ x : X, ∑ z : Z, ∑ u : V,
        (if L x = u then f x else 0) * (if R z = y-u then g z else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x : X, ∑ z : Z, if L x + R z = y then f x * g z else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      have he : R z = y-L x ↔ L x + R z = y := by
        rw [eq_sub_iff_add_eq]
        constructor <;> intro h <;> simpa only [add_comm] using h
      by_cases h : L x + R z = y
      · rw [if_pos h, if_pos (he.mpr h)]
      · rw [if_neg h, if_neg (fun hz => h (he.mp hz)), mul_zero]
    _ = marginal (fun p : X × Z => L p.1 + R p.2)
        (fun p => f p.1 * g p.2) y := by
      rw [marginal, Fintype.sum_prod_type]

theorem pair_sum_eq_convolution {V : Type*}
    [Fintype V] [DecidableEq V] [AddCommGroup V] (f g : V → ℝ) :
    marginal (fun p : V × V => p.1+p.2) (fun p => f p.1*g p.2) = convolution f g := by
  simpa only [marginal_id] using
    pair_marginal_eq_convolution (fun x : V => x) (fun x : V => x) f g

theorem sum_fin_four {A : Type*} [AddCommMonoid A] (f : Fin 4 → A) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + f 3)) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem prod_fin_four (f : Fin 4 → ℝ) :
    (∏ i, f i) = f 0 * (f 1 * (f 2 * f 3)) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rfl

/-- Two pairs of source labels, used only as a finite summation equivalence. -/
def fourTupleEquiv (V : Type*) : (Fin 4 → V) ≃ (V × V) × (V × V) where
  toFun x := ((x 0,x 1),(x 2,x 3))
  invFun p i := if i=0 then p.1.1 else if i=1 then p.1.2 else if i=2 then p.2.1 else p.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl

theorem sum_fourTupleEquiv {V : Type*} [AddCommMonoid V] (p : (V × V) × (V × V)) :
    (∑ i : Fin 4, (fourTupleEquiv V).symm p i) = (p.1.1+p.1.2)+(p.2.1+p.2.2) := by
  rw [sum_fin_four]
  change p.1.1+(p.1.2+(p.2.1+p.2.2)) = _
  exact (add_assoc _ _ _).symm

theorem prod_fourTupleEquiv {V : Type*} (f : Fin 4 → V → ℝ)
    (p : (V × V) × (V × V)) :
    (∏ i : Fin 4, f i ((fourTupleEquiv V).symm p i)) =
      (f 0 p.1.1*f 1 p.1.2)*(f 2 p.2.1*f 3 p.2.2) := by
  rw [prod_fin_four]
  change f 0 p.1.1*(f 1 p.1.2*(f 2 p.2.1*f 3 p.2.2)) = _
  exact (mul_assoc _ _ _).symm

/-- The pushforward of four product weights has the balanced convolution form. -/
theorem four_marginal_eq_convolution {V : Type*}
    [Fintype V] [DecidableEq V] [AddCommGroup V] (f : Fin 4 → V → ℝ) :
    marginal (fun x : Fin 4 → V => ∑ i, x i) (fun x => ∏ i, f i (x i)) =
      convolution (convolution (f 0) (f 1)) (convolution (f 2) (f 3)) := by
  calc
    _ = marginal (fun p : (V × V) × (V × V) => (p.1.1+p.1.2)+(p.2.1+p.2.2))
        (fun p => (f 0 p.1.1*f 1 p.1.2)*(f 2 p.2.1*f 3 p.2.2)) := by
      funext y
      have h := Equiv.sum_comp (fourTupleEquiv V).symm
        (fun x : Fin 4 → V => if (∑ i, x i) = y then ∏ i, f i (x i) else 0)
      simpa only [marginal, sum_fourTupleEquiv, prod_fourTupleEquiv] using h.symm
    _ = convolution
        (marginal (fun p : V × V => p.1+p.2) (fun p => f 0 p.1*f 1 p.2))
        (marginal (fun p : V × V => p.1+p.2) (fun p => f 2 p.1*f 3 p.2)) :=
      pair_marginal_eq_convolution
        (fun p : V × V => p.1+p.2) (fun p : V × V => p.1+p.2)
        (fun p : V × V => f 0 p.1*f 1 p.2) (fun p : V × V => f 2 p.1*f 3 p.2)
    _ = _ := by rw [pair_sum_eq_convolution, pair_sum_eq_convolution]

/-- Independent relabeling changes the source densities by inverse weights. -/
theorem relabeled_four_marginal {V : Type*}
    [Fintype V] [DecidableEq V] [AddCommGroup V]
    (L : Fin 4 → Equiv.Perm V) (f : Fin 4 → V → ℝ) :
    marginal (fun x : Fin 4 → V => ∑ i, L i (x i)) (fun x => ∏ i, f i (x i)) =
      convolution
        (convolution (lawRelabel (L 0) (f 0)) (lawRelabel (L 1) (f 1)))
        (convolution (lawRelabel (L 2) (f 2)) (lawRelabel (L 3) (f 3))) := by
  have h := marginal_relabel (Equiv.piCongrRight L)
    (fun x : Fin 4 → V => ∏ i, f i (x i)) (fun x : Fin 4 → V => ∑ i, x i)
  change marginal (fun x : Fin 4 → V => ∑ i, x i)
      (fun x => ∏ i, lawRelabel (L i) (f i) (x i)) =
    marginal (fun x : Fin 4 → V => ∑ i, L i (x i)) (fun x => ∏ i, f i (x i)) at h
  rw [← h]
  exact four_marginal_eq_convolution _

end AESPaper.ManySourceMarginal
