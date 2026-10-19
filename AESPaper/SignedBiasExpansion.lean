import AESPaper.PureBiasBounds
import AESConcrete.RestrictedMarginalEnergy
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact signed expansion of a bias-weighted joint marginal

The bias product expands over its selected coordinate subsets before any
norm estimate. Each summand keeps the original signed joint density and an
unnormalized distinguished-coordinate restriction. Finite-sum linearity then
transports that identity through an arbitrary marginal and an arbitrary
possibly signed kernel. No normalization or coordinate independence is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.SignedBiasExpansion
open AESMixing AESPaper.BiasTensorEnergy
open AESConcrete.RestrictedMarginalEnergy (marginal)

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Q" => (Fintype.card V : ℝ)

/-- Restriction preserves the original weight; no event probability is divided out. -/
def zeroRestricted (z : V) (D : Finset (Fin 4))
    (g : (Fin 4 → V) → ℝ) (x : Fin 4 → V) : ℝ :=
  if (∀ i ∈ D, x i = z) then g x else 0

/-- The sign counts the unselected bias factors, each contributing `-1`. -/
def signedCoefficient (S D : Finset (Fin 4)) : ℝ :=
  (-1 : ℝ) ^ (S.card - D.card) * Q ^ D.card

theorem zeroRestricted_empty (z : V) (g : (Fin 4 → V) → ℝ) :
    zeroRestricted z ∅ g = g := by
  funext x
  simp [zeroRestricted]

theorem signedCoefficient_abs (S D : Finset (Fin 4)) :
    |signedCoefficient (V := V) S D| = Q ^ D.card := by
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  simp [signedCoefficient, abs_mul, abs_pow, abs_of_nonneg hQ]

theorem indicator_product (z : V) (D : Finset (Fin 4)) (x : Fin 4 → V) :
    (∏ i ∈ D, if x i = z then (1 : ℝ) else 0) =
      if (∀ i ∈ D, x i = z) then 1 else 0 := by
  by_cases hz : ∀ i ∈ D, x i = z
  · rw [if_pos hz]
    exact Finset.prod_eq_one (fun i hi => if_pos (hz i hi))
  · rw [if_neg hz]
    push_neg at hz
    obtain ⟨i, hi, hxi⟩ := hz
    exact Finset.prod_eq_zero hi (if_neg hxi)

theorem scaled_indicator_product (z : V) (D : Finset (Fin 4))
    (x : Fin 4 → V) :
    (∏ i ∈ D, Q * (if x i = z then (1 : ℝ) else 0)) =
      Q ^ D.card * (if (∀ i ∈ D, x i = z) then 1 else 0) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, indicator_product]

theorem basisProduct_finset (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V) :
    basisProduct z S x = ∏ i ∈ S, basis z (x i) := by
  simp only [basisProduct, Finset.prod_ite_mem_eq]

/-- Exact vector expansion, retaining every joint zero event and its sign. -/
theorem basisProduct_expansion (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V) :
    basisProduct z S x = ∑ D ∈ S.powerset,
      signedCoefficient (V := V) S D *
        (if (∀ i ∈ D, x i = z) then 1 else 0) := by
  calc
    _ = ∏ i ∈ S, (Q * (if x i = z then (1 : ℝ) else 0) + (-1)) := by
      simp only [basisProduct_finset, PureBiasBounds.basis_eq_indicator,
        sub_eq_add_neg]
    _ = ∑ D ∈ S.powerset,
        (∏ i ∈ D, Q * (if x i = z then (1 : ℝ) else 0)) *
          ∏ i ∈ S \ D, (-1 : ℝ) :=
      Finset.prod_add (fun i => Q * (if x i = z then (1 : ℝ) else 0))
        (fun _ => (-1 : ℝ)) S
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [scaled_indicator_product, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hD)]
      unfold signedCoefficient
      ring

/-- Multiplication by an arbitrary signed law preserves the exact expansion. -/
theorem weighted_density_expansion (z : V) (S : Finset (Fin 4))
    (g : (Fin 4 → V) → ℝ) (x : Fin 4 → V) :
    g x * basisProduct z S x = ∑ D ∈ S.powerset,
      signedCoefficient (V := V) S D * zeroRestricted z D g x := by
  rw [basisProduct_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  by_cases hz : ∀ i ∈ D, x i = z <;> simp [zeroRestricted, hz] <;> ring

section FiniteLinearity
variable {X Y J : Type*} [Fintype X] [Fintype Y]
  [DecidableEq Y] [DecidableEq J]

/-- Marginal pushforward is linear over any finite signed family. -/
theorem marginal_finset_linear (coord : X → Y) (s : Finset J)
    (c : J → ℝ) (f : J → X → ℝ) (y : Y) :
    marginal coord (fun x => ∑ j ∈ s, c j * f j x) y =
      ∑ j ∈ s, c j * marginal coord (f j) y := by
  unfold marginal
  have hp (x : X) :
      (if coord x = y then ∑ j ∈ s, c j * f j x else 0) =
        ∑ j ∈ s, c j * (if coord x = y then f j x else 0) := by
    by_cases hx : coord x = y <;> simp [hx]
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

/-- A finite signed family passes through any kernel without an order argument. -/
theorem action_finset_linear (K : Y → X → ℝ) (s : Finset J)
    (c : J → ℝ) (f : J → X → ℝ) (y : Y) :
    action K (fun x => ∑ j ∈ s, c j * f j x) y =
      ∑ j ∈ s, c j * action K (f j) y := by
  unfold action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteLinearity

section Marginal
variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The weighted marginal is a signed sum of unnormalized event marginals. -/
theorem weighted_marginal_expansion (z : V) (S : Finset (Fin 4))
    (coord : (Fin 4 → V) → Y) (g : (Fin 4 → V) → ℝ) (y : Y) :
    marginal coord (fun x => g x * basisProduct z S x) y =
      ∑ D ∈ S.powerset, signedCoefficient (V := V) S D *
        marginal coord (zeroRestricted z D g) y := by
  have h : (fun x => g x * basisProduct z S x) =
      (fun x => ∑ D ∈ S.powerset,
        signedCoefficient (V := V) S D * zeroRestricted z D g x) := by
    funext x
    exact weighted_density_expansion z S g x
  rw [h]
  exact marginal_finset_linear coord S.powerset
    (signedCoefficient (V := V) S) (fun D => zeroRestricted z D g) y

/-- Exact response identity, valid even when the density and kernel are signed. -/
theorem weighted_response_expansion (z : V) (S : Finset (Fin 4))
    (coord : (Fin 4 → V) → Y) (g : (Fin 4 → V) → ℝ)
    (K : Y → Y → ℝ) (y : Y) :
    action K (marginal coord (fun x => g x * basisProduct z S x)) y =
      ∑ D ∈ S.powerset, signedCoefficient (V := V) S D *
        action K (marginal coord (zeroRestricted z D g)) y := by
  have h : marginal coord (fun x => g x * basisProduct z S x) =
      (fun v => ∑ D ∈ S.powerset, signedCoefficient (V := V) S D *
        marginal coord (zeroRestricted z D g) v) := by
    funext v
    exact weighted_marginal_expansion z S coord g v
  rw [h]
  exact action_finset_linear K S.powerset (signedCoefficient (V := V) S)
    (fun D => marginal coord (zeroRestricted z D g)) y

end Marginal
end AESPaper.SignedBiasExpansion
