/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.Imports
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Generic collision sums on explicitly parameterized finite fibers

The information-set branch uses a bijection with all assignments to the
chosen coordinates.  The remaining coordinate factors need only a pointwise
cap; no independence of those coordinates is assumed.  The other branch uses
an explicit, constant cardinality for every fiber of the observed projection.
These are the two finite-sum mechanisms in the manuscript's collision lemma.

The existing `CodeMoment.low_dimension_code_moment` concerns two information
sets and a Gram square sum, so it is a different estimate.  We use the standard
finite product-sum and fiberwise-sum identities directly.  Exact prescribed
coordinate counts are already supplied by `CoordinateCount`'s
`AESMixing.bijective_prescribed_card`; they are not reproved here.

These generic hypotheses still require actual code/fiber instantiation.  No
MDS property, affine dimension formula, AES local bound, or transfer/return
operator estimate is inferred from the sums below.  Constructive proof work
only; no attacks or predecessor/manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.FiberCollision

section CoordinateSums
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]

/-- Full coordinate assignment sums factor, with a different function per coordinate. -/
theorem coordinate_product_sum_bound (g : I → V → ℝ) (h : ℝ)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgsum : ∀ i, (∑ x, g i x) ≤ h) :
    (∑ u : I → V, ∏ i, g i (u i)) ≤ h ^ Fintype.card I := by
  calc
    (∑ u : I → V, ∏ i, g i (u i)) = ∏ i : I, ∑ x : V, g i x :=
      (Fintype.prod_sum g).symm
    _ ≤ ∏ _ : I, h := Finset.prod_le_prod
      (fun i _ => Finset.sum_nonneg (fun x _ => hg0 i x)) (fun i _ => hgsum i)
    _ = h ^ Fintype.card I := by simp

end CoordinateSums

section InformationSet
variable {C V I J : Type*} [Fintype C] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq I]

/-- Information-set case: sum over its free coordinates and cap the rest.
For a fiber of dimension `a ≤ n`, instantiate `card I = a` and `card J = n-a`. -/
theorem information_set_sum_bound (e : C ≃ (I → V)) (rest : C → J → V)
    (g : I → V → ℝ) (r : J → V → ℝ) (h delta : ℝ)
    (hd : 0 ≤ delta) (hg0 : ∀ i x, 0 ≤ g i x)
    (hr0 : ∀ j x, 0 ≤ r j x) (hgsum : ∀ i, (∑ x, g i x) ≤ h)
    (hrcap : ∀ j x, r j x ≤ delta) :
    (∑ c : C, (∏ i, g i (e c i)) * (∏ j, r j (rest c j))) ≤
      h ^ Fintype.card I * delta ^ Fintype.card J := by
  have hrest (c : C) : (∏ j, r j (rest c j)) ≤ delta ^ Fintype.card J := by
    calc
      (∏ j, r j (rest c j)) ≤ ∏ _ : J, delta :=
        Finset.prod_le_prod (fun j _ => hr0 j _) (fun j _ => hrcap j _)
      _ = delta ^ Fintype.card J := by simp
  have hinfo : (∑ c : C, ∏ i, g i (e c i)) ≤ h ^ Fintype.card I := by
    calc
      (∑ c : C, ∏ i, g i (e c i)) = ∑ u : I → V, ∏ i, g i (u i) :=
        e.sum_comp (fun u => ∏ i, g i (u i))
      _ ≤ h ^ Fintype.card I := coordinate_product_sum_bound g h hg0 hgsum
  calc
    (∑ c : C, (∏ i, g i (e c i)) * (∏ j, r j (rest c j))) ≤
        ∑ c : C, (∏ i, g i (e c i)) * delta ^ Fintype.card J := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (hrest c)
        (Finset.prod_nonneg (fun i _ => hg0 i _))
    _ = (∑ c : C, ∏ i, g i (e c i)) * delta ^ Fintype.card J :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ h ^ Fintype.card I * delta ^ Fintype.card J :=
      mul_le_mul_of_nonneg_right hinfo (pow_nonneg hd _)

end InformationSet

section ConstantFibers
variable {C B : Type*} [Fintype C] [Fintype B] [DecidableEq B]

/-- Exact weighted pushforward when every observed value has `m` preimages.
Weights may have either sign; nonnegativity enters only the later bound. -/
theorem constant_fiber_sum (proj : C → B) (m : ℕ)
    (hfiber : ∀ b, Fintype.card {c : C // proj c = b} = m) (w : B → ℝ) :
    (∑ c : C, w (proj c)) = (m : ℝ) * ∑ b : B, w b := by
  rw [← Fintype.sum_fiberwise' proj w]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber]
  rw [Finset.mul_sum]

end ConstantFibers

section ObservedCoordinates
variable {C V I : Type*} [Fintype C] [Fintype V] [Fintype I]
  [DecidableEq I] [DecidableEq V]

/-- Exact collision sum with constant fibers over the full observed tuple space. -/
theorem constant_fiber_product_sum (proj : C → (I → V)) (m : ℕ)
    (hfiber : ∀ u, Fintype.card {c : C // proj c = u} = m)
    (g : I → V → ℝ) :
    (∑ c : C, ∏ i, g i (proj c i)) = (m : ℝ) * ∏ i : I, ∑ x : V, g i x := by
  calc
    (∑ c : C, ∏ i, g i (proj c i)) =
        (m : ℝ) * ∑ u : I → V, ∏ i, g i (u i) :=
      constant_fiber_sum proj m hfiber (fun u => ∏ i, g i (u i))
    _ = (m : ℝ) * ∏ i : I, ∑ x : V, g i x := by
      rw [← Fintype.prod_sum]

/-- Constant-fiber case: each observed assignment contributes exactly `m` times.
For a fiber dimension `a > n`, the code-specific obligation is `m = q^(a-n)`
and `card I = n`; this theorem assumes only the displayed cardinalities. -/
theorem constant_fiber_projection_sum_bound (proj : C → (I → V)) (m : ℕ)
    (hfiber : ∀ u, Fintype.card {c : C // proj c = u} = m)
    (g : I → V → ℝ) (h : ℝ)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgsum : ∀ i, (∑ x, g i x) ≤ h) :
    (∑ c : C, ∏ i, g i (proj c i)) ≤ (m : ℝ) * h ^ Fintype.card I := by
  rw [constant_fiber_sum proj m hfiber (fun u => ∏ i, g i (u i))]
  exact mul_le_mul_of_nonneg_left (coordinate_product_sum_bound g h hg0 hgsum)
    (Nat.cast_nonneg m)

end ObservedCoordinates

end AES8.FiberCollision
