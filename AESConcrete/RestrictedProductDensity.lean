import AESMixing.Product
import Mathlib.Tactic.Ring

/-!
# Restricted product-source densities and their energy

The free input laws are actual factors in an explicitly defined product.
An arbitrary event indicator and omitted-coordinate factors remain in the
restricted density. Point bounds on the omitted factors give the precise
power loss, independently of their dependence on the free inputs.

This generic finite-algebra module assumes no MDS correspondence or output
channel bound. Constructive mathematics only; no attacks, manuscript or
historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.RestrictedProductDensity

variable {I J V C : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype V] [Fintype C]

def productDensity (mu : I → V → ℝ) (x : I → V) : ℝ :=
  ∏ i : I, mu i (x i)

theorem productDensity_nonneg (mu : I → V → ℝ)
    (hmu : ∀ i v, 0 ≤ mu i v) (x : I → V) :
    0 ≤ productDensity mu x :=
  Finset.prod_nonneg (fun i _ => hmu i (x i))

/-- Exact mass factorization; signed factors are permitted in this identity. -/
theorem productDensity_mass (mu : I → V → ℝ) :
    (∑ x : I → V, productDensity mu x) = ∏ i : I, ∑ v : V, mu i v :=
  (Fintype.prod_sum mu).symm

theorem productDensity_mass_one (mu : I → V → ℝ)
    (hmass : ∀ i, (∑ v : V, mu i v) = 1) :
    (∑ x : I → V, productDensity mu x) = 1 := by
  rw [productDensity_mass]
  simp only [hmass, Finset.prod_const_one]

/-- Collision is derived from finite product-of-sums algebra. -/
theorem productDensity_energy (mu : I → V → ℝ) :
    (∑ x : I → V, productDensity mu x ^ 2) = ∏ i : I, ∑ v : V, mu i v ^ 2 :=
  AESMixing.product_column_energy mu

theorem productDensity_energy_le (mu : I → V → ℝ) (rho : ℝ)
    (hcollision : ∀ i, (∑ v : V, mu i v ^ 2) ≤ rho) :
    (∑ x : I → V, productDensity mu x ^ 2) ≤ rho ^ Fintype.card I :=
  AESMixing.product_column_energy_le mu rho hcollision

theorem productDensity_point_bound (mu : I → V → ℝ) (p : ℝ)
    (hmu : ∀ i v, 0 ≤ mu i v) (hpoint : ∀ i v, mu i v ≤ p) (x : I → V) :
    productDensity mu x ≤ p ^ Fintype.card I := by
  calc
    _ ≤ ∏ _ : I, p := Finset.prod_le_prod
      (fun i _ => hmu i (x i)) (fun i _ => hpoint i (x i))
    _ = _ := by simp

/-- Source energy under arbitrary nonnegative domination and reparametrization. -/
theorem dominated_source_energy (e : C ≃ (I → V))
    (mu : I → V → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hmu : ∀ i v, 0 ≤ mu i v)
    (hcollision : ∀ i, (∑ v : V, mu i v ^ 2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * productDensity mu (e c)) :
    (∑ c : C, g c ^ 2) ≤ scale^2 * rho ^ Fintype.card I := by
  have hs (c : C) : g c ^ 2 ≤ (scale * productDensity mu (e c))^2 :=
    (sq_le_sq₀ (hg c) (mul_nonneg hscale (productDensity_nonneg mu hmu (e c)))).mpr
      (hdom c)
  calc
    _ ≤ ∑ c : C, (scale * productDensity mu (e c))^2 :=
      Finset.sum_le_sum (fun c _ => hs c)
    _ = scale^2 * ∑ c : C, productDensity mu (e c)^2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ = scale^2 * ∑ x : I → V, productDensity mu x^2 := by
      rw [Equiv.sum_comp e (fun x : I → V => productDensity mu x^2)]
    _ ≤ scale^2 * rho ^ Fintype.card I := mul_le_mul_of_nonneg_left
      (productDensity_energy_le mu rho hcollision) (sq_nonneg scale)

/-- Omitted-coordinate laws and the arbitrary event are never normalized away. -/
def restrictedDensity (e : C ≃ (I → V)) (mu : I → V → ℝ) (nu : J → V → ℝ)
    (extra : C → J → V) (event : C → Prop) [DecidablePred event] (c : C) : ℝ :=
  if event c then productDensity mu (e c) * productDensity nu (extra c) else 0

theorem restrictedDensity_nonneg (e : C ≃ (I → V)) (mu : I → V → ℝ) (nu : J → V → ℝ)
    (extra : C → J → V) (event : C → Prop) [DecidablePred event]
    (hmu : ∀ i v, 0 ≤ mu i v) (hnu : ∀ j v, 0 ≤ nu j v) (c : C) :
    0 ≤ restrictedDensity e mu nu extra event c := by
  unfold restrictedDensity
  split_ifs
  · exact mul_nonneg (productDensity_nonneg mu hmu _) (productDensity_nonneg nu hnu _)
  · exact le_rfl

theorem restrictedDensity_domination (e : C ≃ (I → V)) (mu : I → V → ℝ) (nu : J → V → ℝ)
    (extra : C → J → V) (event : C → Prop) [DecidablePred event] (p : ℝ)
    (hp : 0 ≤ p) (hmu : ∀ i v, 0 ≤ mu i v) (hnu : ∀ j v, 0 ≤ nu j v)
    (hpoint : ∀ j v, nu j v ≤ p) (c : C) :
    restrictedDensity e mu nu extra event c ≤ p ^ Fintype.card J * productDensity mu (e c) := by
  unfold restrictedDensity
  split_ifs
  · calc
      _ ≤ productDensity mu (e c) * p ^ Fintype.card J :=
        mul_le_mul_of_nonneg_left (productDensity_point_bound nu p hnu hpoint (extra c))
          (productDensity_nonneg mu hmu (e c))
      _ = _ := mul_comm _ _
  · exact mul_nonneg (pow_nonneg hp _) (productDensity_nonneg mu hmu (e c))

/-- The shortened-source energy loss is exactly two powers per omitted factor. -/
theorem restrictedDensity_energy_le (e : C ≃ (I → V)) (mu : I → V → ℝ) (nu : J → V → ℝ)
    (extra : C → J → V) (event : C → Prop) [DecidablePred event] (p rho : ℝ)
    (hp : 0 ≤ p) (hmu : ∀ i v, 0 ≤ mu i v) (hnu : ∀ j v, 0 ≤ nu j v)
    (hpoint : ∀ j v, nu j v ≤ p)
    (hcollision : ∀ i, (∑ v : V, mu i v^2) ≤ rho) :
    (∑ c : C, restrictedDensity e mu nu extra event c ^ 2) ≤
      p ^ (2 * Fintype.card J) * rho ^ Fintype.card I := by
  have h := dominated_source_energy e mu (restrictedDensity e mu nu extra event)
    (p ^ Fintype.card J) rho hmu hcollision (pow_nonneg hp _)
    (restrictedDensity_nonneg e mu nu extra event hmu hnu)
    (restrictedDensity_domination e mu nu extra event p hp hmu hnu hpoint)
  simpa only [← pow_mul, Nat.mul_comm] using h

end AESConcrete.RestrictedProductDensity
