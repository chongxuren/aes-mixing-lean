import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Ring

/-!
# Normalized averaging along one additive translation family

For the intended residual-pair application, take `X = V × V`. The signed
amplitude is arbitrary and joint: no factorization, marginal centering, axis-
zero condition or positivity is assumed. The average is over one common
parameter `z`, rather than independent averages over the two coordinates.

The averaging statements do not need injectivity of `D`. An actual retained
fiber is connected to this average only through an explicit finite equivalence
and the affine residual-coordinate identity in
`fiber_sum_eq_card_mul_average`. Constructing that equivalence, the AES/MDS
geometry, the subsequent fiber-count energy identity, and any physical cap
remain separate obligations.

Constructive fixed independent-key AES10/14/16 scope is preserved: whitening,
omitted final MixColumns, and ordered-distinct reference law.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledLineAverage

section Basic
variable {V X : Type*} [Fintype V] [AddCommGroup V] [AddCommGroup X]

/-- Average over a single additive parameter. In the pair specialization,
both coordinates of `D z` use the same `z`. -/
def average (D : V →+ X) (h : X → ℝ) (x : X) : ℝ :=
  (∑ z, h (x + D z)) / (Fintype.card V : ℝ)

/-- The unnormalized parameter sum has exactly one cardinality factor. -/
theorem sum_eq_card_mul_average (D : V →+ X) (h : X → ℝ) (x : X) :
    (∑ z, h (x + D z)) = (Fintype.card V : ℝ) * average D h x := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  field_simp [hn]

/-- Translation by the image of `D` reindexes the same finite average. -/
theorem average_translation (D : V →+ X) (h : X → ℝ) (x : X) (t : V) :
    average D h (x + D t) = average D h x := by
  classical
  unfold average
  congr 1
  have he := Equiv.sum_comp (Equiv.addRight t) (fun z : V => h (x + D z))
  change (∑ z : V, h (x + D (z + t))) = ∑ z : V, h (x + D z) at he
  simpa only [map_add, add_assoc, add_left_comm, add_comm] using he

/-- The normalized average is a projection onto its translation-invariant
image. This does not assert that the projection vanishes. -/
theorem average_idempotent (D : V →+ X) (h : X → ℝ) :
    average D (average D h) = average D h := by
  classical
  funext x
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (∑ z, average D h (x + D z)) / (Fintype.card V : ℝ) = average D h x
  simp only [average_translation, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]

/-- Exact fiber interface: `S` may be a retained-map fiber, but its
parameterization and affine residual-coordinate law are supplied explicitly.
No AES geometry, injectivity claim or fiber cardinality is inferred here. -/
theorem fiber_sum_eq_card_mul_average {S : Type*} [Fintype S]
    (D : V →+ X) (h : X → ℝ) (e : V ≃ S) (residual : S → X) (x : X)
    (hresidual : ∀ z, residual (e z) = x + D z) :
    (∑ s, h (residual s)) = (Fintype.card V : ℝ) * average D h x := by
  calc
    (∑ s, h (residual s)) = ∑ z : V, h (residual (e z)) :=
      (e.sum_comp (fun s => h (residual s))).symm
    _ = ∑ z : V, h (x + D z) := by simp only [hresidual]
    _ = (Fintype.card V : ℝ) * average D h x :=
      sum_eq_card_mul_average D h x

end Basic

section Energy
variable {V X : Type*} [Fintype V] [AddCommGroup V]
  [Fintype X] [AddCommGroup X]

/-- Normalized coupled-line averaging contracts counting-measure squared
energy for every signed joint amplitude. No injectivity of `D` is required. -/
theorem average_energy (D : V →+ X) (h : X → ℝ) :
    (∑ x, average D h x ^ 2) ≤ ∑ x, h x ^ 2 := by
  classical
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn
  -- Cauchy--Schwarz is applied before summing over the ambient space.
  have hpoint (x : X) :
      average D h x ^ 2 ≤ (∑ z, h (x + D z) ^ 2) / (Fintype.card V : ℝ) := by
    have hcs : (∑ z, h (x + D z)) ^ 2 ≤
        (Fintype.card V : ℝ) * ∑ z, h (x + D z) ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : V => (1 : ℝ)) (fun z => h (x + D z))
    unfold average
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    calc
      _ ≤ (Fintype.card V : ℝ) * ∑ z, h (x + D z) ^ 2 := hcs
      _ = ((∑ z, h (x + D z) ^ 2) / (Fintype.card V : ℝ)) *
          (Fintype.card V : ℝ) ^ 2 := by
        field_simp [hn0]
  -- Every ambient translation is a bijection, independently of whether `D`
  -- is injective. This is the exact cancellation of the remaining factor q.
  have hshift (z : V) : (∑ x, h (x + D z) ^ 2) = ∑ x, h x ^ 2 := by
    exact Equiv.sum_comp (Equiv.addRight (D z)) (fun x : X => h x ^ 2)
  calc
    (∑ x, average D h x ^ 2) ≤
        ∑ x, (∑ z, h (x + D z) ^ 2) / (Fintype.card V : ℝ) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (∑ z : V, ∑ x : X, h (x + D z) ^ 2) / (Fintype.card V : ℝ) := by
      rw [← Finset.sum_div, Finset.sum_comm]
    _ = ((Fintype.card V : ℝ) * ∑ x, h x ^ 2) / (Fintype.card V : ℝ) := by
      congr 1
      simp_rw [hshift]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x, h x ^ 2 := by field_simp [hn0]

end Energy
end AESConcrete.CoupledLineAverage
