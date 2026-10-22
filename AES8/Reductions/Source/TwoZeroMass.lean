/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwoZeroResponseEnergy

/-!
# Signed full masses on a two-coordinate information domain

Two literal coordinate pairs are used separately as information bijections.
Cauchy retains the same original source x in all four legs. The bound is on
the signed full mass before any nonzero endpoint subtraction. No source
factorization, absolute Gram replacement or AES estimate is assumed here.

Constructive work only; no attacks or predecessor/manuscript edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwoZeroMass
open AESMixing
variable {V G : Type*} [Fintype V] [Fintype G]

theorem pair_trace_le (A B : V → V → ℝ) (a b : Equiv.Perm V)
    (coords : G → V × V) (hinfo : Function.Bijective coords)
    (delta tau : ℝ) (hd : 0 ≤ delta)
    (hcolumn : ∀ x, (∑ y, A y x ^ 2) ≤ delta)
    (htrace : (∑ y, ∑ x, B y x ^ 2) ≤ tau) :
    (∑ w : G × V, (A (coords w.1).1 (a w.2) * B (coords w.1).2 (b w.2)) ^ 2) ≤
      delta * tau := by
  have hpoint (x : V) :
      (∑ g : G, (A (coords g).1 (a x) * B (coords g).2 (b x)) ^ 2) =
        (∑ y, A y (a x) ^ 2) * (∑ y, B y (b x) ^ 2) := by
    rw [TwoZeroResponseEnergy.sum_pair_of_bijective coords hinfo
      (fun y z => (A y (a x) * B z (b x)) ^ 2)]
    exact TwoZeroResponseEnergy.pair_product_energy _ _
  have hsum : (∑ x, ∑ y, B y (b x) ^ 2) ≤ tau := by
    rw [Equiv.sum_comp b (fun x => ∑ y, B y x ^ 2), Finset.sum_comm]
    exact htrace
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [hpoint]
  calc
    _ ≤ ∑ x, delta * ∑ y, B y (b x) ^ 2 := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_right (hcolumn (a x))
        (Finset.sum_nonneg (fun y _ => sq_nonneg _)))
    _ = delta * ∑ x, ∑ y, B y (b x) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ delta * tau := mul_le_mul_of_nonneg_left hsum hd

theorem signed_mass_sq_le (A B : G → V → ℝ) (mu : V → ℝ)
    (p alpha beta : ℝ) (ha : 0 ≤ alpha)
    (hmu : ∀ x, |mu x| ≤ p)
    (hA : (∑ w : G × V, A w.1 w.2 ^ 2) ≤ alpha)
    (hB : (∑ w : G × V, B w.1 w.2 ^ 2) ≤ beta) :
    |∑ g, ∑ x, mu x * A g x * B g x| ^ 2 ≤ p ^ 2 * alpha * beta := by
  let u (w : G × V) : ℝ := mu w.2 * A w.1 w.2
  let v (w : G × V) : ℝ := B w.1 w.2
  have hu : (∑ w, u w ^ 2) ≤ p ^ 2 * alpha := by
    have hpoint (w : G × V) : u w ^ 2 ≤ p ^ 2 * A w.1 w.2 ^ 2 := by
      dsimp [u]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (mu w.2)) (hmu w.2) 2)
    calc
      _ ≤ ∑ w : G × V, p ^ 2 * A w.1 w.2 ^ 2 :=
        Finset.sum_le_sum (fun w _ => hpoint w)
      _ = p ^ 2 * ∑ w : G × V, A w.1 w.2 ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ p ^ 2 * alpha := mul_le_mul_of_nonneg_left hA (sq_nonneg p)
  have hv : (∑ w, v w ^ 2) ≤ beta := hB
  have heq : (∑ g, ∑ x, mu x * A g x * B g x) = ∑ w, u w * v w := by
    simp only [Fintype.sum_prod_type, u, v]
  rw [sq_abs, heq]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v).trans
    (mul_le_mul hu hv (Finset.sum_nonneg (fun w _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg p) ha))

theorem response_mass_sq_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ) (p alpha beta : ℝ)
    (ha : 0 ≤ alpha) (hmu : ∀ x, |mu x| ≤ p)
    (hA : (∑ w : G × V,
      (T 0 (coords w.1 0) (e 0 w.2) * T 1 (coords w.1 1) (e 1 w.2)) ^ 2) ≤ alpha)
    (hB : (∑ w : G × V,
      (T 2 (coords w.1 2) (e 2 w.2) * T 3 (coords w.1 3) (e 3 w.2)) ^ 2) ≤ beta) :
    |∑ g, ZeroFiberResponseEnergy.response T e coords mu g| ^ 2 ≤ p ^ 2 * alpha * beta := by
  have heq : (∑ g, ZeroFiberResponseEnergy.response T e coords mu g) =
      ∑ g, ∑ x, mu x * (T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x)) *
        (T 2 (coords g 2) (e 2 x) * T 3 (coords g 3) (e 3 x)) := by
    unfold ZeroFiberResponseEnergy.response
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Fin.prod_univ_four]
    ring
  rw [heq]
  exact signed_mass_sq_le _ _ mu p alpha beta ha hmu hA hB

theorem four_residual_mass_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo01 : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (hinfo23 : Function.Bijective (fun g => (coords g 2, coords g 3)))
    (p delta tau : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    |∑ g, ZeroFiberResponseEnergy.response T e coords mu g| ≤ p * delta * tau := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg hp hd) ht)).mp
  have h := response_mass_sq_le T e coords mu p (delta * tau) (delta * tau)
    (mul_nonneg hd ht) hmu
    (pair_trace_le (T 0) (T 1) (e 0) (e 1) _ hinfo01 delta tau hd (hcolumn 0) (htrace 1))
    (pair_trace_le (T 2) (T 3) (e 2) (e 3) _ hinfo23 delta tau hd (hcolumn 2) (htrace 3))
  calc
    _ ≤ p ^ 2 * (delta * tau) * (delta * tau) := h
    _ = (p * delta * tau) ^ 2 := by ring

theorem three_residual_constant_mass_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo01 : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (hinfo23 : Function.Bijective (fun g => (coords g 2, coords g 3)))
    (p kappa delta tau nu : ℝ) (hp : 0 ≤ p) (hk : 0 ≤ kappa)
    (hd : 0 ≤ delta) (ht : 0 ≤ tau) (hn : 0 ≤ nu) (hkd : kappa * delta ≤ nu ^ 2)
    (hmu : ∀ x, |mu x| ≤ p)
    (hconstant : ∀ x, (∑ y, T 0 y x ^ 2) ≤ kappa)
    (hcolumn2 : ∀ x, (∑ y, T 2 y x ^ 2) ≤ delta)
    (htrace1 : (∑ y, ∑ x, T 1 y x ^ 2) ≤ tau)
    (htrace3 : (∑ y, ∑ x, T 3 y x ^ 2) ≤ tau) :
    |∑ g, ZeroFiberResponseEnergy.response T e coords mu g| ≤ p * tau * nu := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg hp ht) hn)).mp
  have h := response_mass_sq_le T e coords mu p (kappa * tau) (delta * tau)
    (mul_nonneg hk ht) hmu
    (pair_trace_le (T 0) (T 1) (e 0) (e 1) _ hinfo01 kappa tau hk hconstant htrace1)
    (pair_trace_le (T 2) (T 3) (e 2) (e 3) _ hinfo23 delta tau hd hcolumn2 htrace3)
  calc
    _ ≤ p ^ 2 * (kappa * tau) * (delta * tau) := h
    _ = (p ^ 2 * tau ^ 2) * (kappa * delta) := by ring
    _ ≤ (p ^ 2 * tau ^ 2) * nu ^ 2 :=
      mul_le_mul_of_nonneg_left hkd (mul_nonneg (sq_nonneg p) (sq_nonneg tau))
    _ = (p * tau * nu) ^ 2 := by ring

end AES8.TwoZeroMass
