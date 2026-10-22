/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwoZeroResponseEnergy

/-!
# Three residual legs and one bounded constant leg on a two-coordinate domain

The same signed common source is retained in all four response factors.
Cauchy in that source bounds the atom, constant leg and third residual entry;
the remaining two residual rows are summed through their literal information
bijection. Two complete entry-square traces suffice. No absolute-value Gram
moment, coordinate independence, AES numerical cap or geometry is assumed.

Constructive mathematics only; no attacks or predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ThreeResidualConstantEnergy
open AESMixing

variable {V G : Type*} [Fintype V] [Fintype G]

/-- Coordinate 0 is constant, coordinates 1,2 are information residual legs,
and coordinate 3 is the residual entry bounded pointwise. -/
theorem response_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo : Function.Bijective (fun g => (coords g 1, coords g 2)))
    (p kappa epsilon tau : ℝ) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hconstant : ∀ y x, |T 0 y x| ≤ kappa)
    (hentry : ∀ y x, |T 3 y x| ≤ epsilon)
    (htrace1 : (∑ y, ∑ x, T 1 y x ^ 2) ≤ tau)
    (htrace2 : (∑ y, ∑ x, T 2 y x ^ 2) ≤ tau) :
    (∑ g, ZeroFiberResponseEnergy.response T e coords mu g ^ 2) ≤
      p ^ 2 * kappa ^ 2 * epsilon ^ 2 * tau ^ 2 := by
  let K : ℝ := p ^ 2 * kappa ^ 2 * epsilon ^ 2
  let A (g : G) : ℝ := ∑ x, T 1 (coords g 1) (e 1 x) ^ 2
  let B (g : G) : ℝ := ∑ x, T 2 (coords g 2) (e 2 x) ^ 2
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (sq_nonneg kappa)) (sq_nonneg epsilon)
  have hmu_sq (x : V) : mu x ^ 2 ≤ p ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (mu x)) (hmu x) 2)
  have hpoint (g : G) :
      ZeroFiberResponseEnergy.response T e coords mu g ^ 2 ≤ K * (A g * B g) := by
    let u (x : V) : ℝ :=
      mu x * T 0 (coords g 0) (e 0 x) * T 3 (coords g 3) (e 3 x) *
        T 1 (coords g 1) (e 1 x)
    let v (x : V) : ℝ := T 2 (coords g 2) (e 2 x)
    have hu (x : V) : u x ^ 2 ≤ K * T 1 (coords g 1) (e 1 x) ^ 2 := by
      have h0 := TwoZeroResponseEnergy.entry_sq_le (T 0) kappa hconstant
        (coords g 0) (e 0 x)
      have h3 := TwoZeroResponseEnergy.entry_sq_le (T 3) epsilon hentry
        (coords g 3) (e 3 x)
      have hc : mu x ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 *
          T 3 (coords g 3) (e 3 x) ^ 2 ≤ K :=
        mul_le_mul (mul_le_mul (hmu_sq x) h0 (sq_nonneg _) (sq_nonneg p)) h3
          (sq_nonneg _) (mul_nonneg (sq_nonneg p) (sq_nonneg kappa))
      calc
        _ = (mu x ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 *
            T 3 (coords g 3) (e 3 x) ^ 2) * T 1 (coords g 1) (e 1 x) ^ 2 := by
          dsimp only [u]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    have hsum : (∑ x, u x ^ 2) ≤ K * A g := by
      calc
        _ ≤ ∑ x, K * T 1 (coords g 1) (e 1 x) ^ 2 :=
          Finset.sum_le_sum (fun x _ => hu x)
        _ = _ := (Finset.mul_sum _ _ _).symm
    have heq : ZeroFiberResponseEnergy.response T e coords mu g = ∑ x, u x * v x := by
      unfold ZeroFiberResponseEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      simp only [u, v, Fin.prod_univ_four]
      ring
    rw [heq]
    calc
      _ ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
      _ ≤ (K * A g) * B g :=
        mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg (fun x _ => sq_nonneg _))
      _ = _ := by ring
  have ht1 : (∑ y, ∑ x, T 1 y (e 1 x) ^ 2) ≤ tau := by
    have hs (y : V) : (∑ x, T 1 y (e 1 x) ^ 2) = ∑ x, T 1 y x ^ 2 :=
      Equiv.sum_comp (e 1) (fun x => T 1 y x ^ 2)
    simpa only [hs] using htrace1
  have ht2 : (∑ y, ∑ x, T 2 y (e 2 x) ^ 2) ≤ tau := by
    have hs (y : V) : (∑ x, T 2 y (e 2 x) ^ 2) = ∑ x, T 2 y x ^ 2 :=
      Equiv.sum_comp (e 2) (fun x => T 2 y x ^ 2)
    simpa only [hs] using htrace2
  have hinfo_energy : (∑ g, A g * B g) ≤ tau ^ 2 := by
    calc
      _ = (∑ a, ∑ x, T 1 a (e 1 x) ^ 2) * (∑ b, ∑ x, T 2 b (e 2 x) ^ 2) := by
        dsimp only [A, B]
        rw [TwoZeroResponseEnergy.sum_pair_of_bijective
          (fun g => (coords g 1, coords g 2)) hinfo
          (fun a b => (∑ x, T 1 a (e 1 x) ^ 2) * (∑ x, T 2 b (e 2 x) ^ 2))]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ tau * tau :=
        mul_le_mul ht1 ht2
          (Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun x _ => sq_nonneg _))) ht
      _ = _ := by ring
  calc
    _ ≤ ∑ g, K * (A g * B g) := Finset.sum_le_sum (fun g _ => hpoint g)
    _ = K * ∑ g, A g * B g := (Finset.mul_sum _ _ _).symm
    _ ≤ K * tau ^ 2 := mul_le_mul_of_nonneg_left hinfo_energy hK
    _ = _ := by rfl

end AES8.ThreeResidualConstantEnergy
