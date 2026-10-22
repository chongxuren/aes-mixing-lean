/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ThreeZeroResponseEnergy

/-!
# Signed common-source masses on one-coordinate information domains

An information-coordinate bijection and permutation of the SAME original
source label are used on both Cauchy factors. No absolute Gram replacement or
independence of the four current coordinates is used.
Constructive proof work only; no attacks or proof bypasses.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ThreeZeroMass
open AESMixing
variable {V G : Type*} [Fintype V] [Fintype G]

theorem mixed_trace_le (T : V → V → ℝ) (e : Equiv.Perm V)
    (coords : G → V) (hinfo : Function.Bijective coords) (tau : ℝ)
    (htrace : (∑ y, ∑ x, T y x ^ 2) ≤ tau) :
    (∑ w : G × V, T (coords w.1) (e w.2) ^ 2) ≤ tau := by
  simp only [Fintype.sum_prod_type]
  exact ThreeZeroResponseEnergy.trace_information_le T e coords hinfo tau htrace

theorem signed_mass_le_two_traces
    (A B U : G → V → ℝ) (K tau : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ tau)
    (hU : ∀ g x, |U g x| ≤ K)
    (hA : (∑ w : G × V, A w.1 w.2 ^ 2) ≤ tau)
    (hB : (∑ w : G × V, B w.1 w.2 ^ 2) ≤ tau) :
    |∑ g, ∑ x, U g x * A g x * B g x| ≤ K * tau := by
  let u (w : G × V) : ℝ := U w.1 w.2 * A w.1 w.2
  let v (w : G × V) : ℝ := B w.1 w.2
  have hu : (∑ w, u w ^ 2) ≤ K ^ 2 * tau := by
    have hp (w : G × V) : u w ^ 2 ≤ K ^ 2 * A w.1 w.2 ^ 2 := by
      dsimp [u]
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (U w.1 w.2)) (hU w.1 w.2) 2)
    calc
      _ ≤ ∑ w, K ^ 2 * A w.1 w.2 ^ 2 := Finset.sum_le_sum (fun w _ => hp w)
      _ = K ^ 2 * ∑ w : G × V, A w.1 w.2 ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ K ^ 2 * tau := mul_le_mul_of_nonneg_left hA (sq_nonneg K)
  have hv : (∑ w, v w ^ 2) ≤ tau := hB
  have heq : (∑ g, ∑ x, U g x * A g x * B g x) = ∑ w, u w * v w := by
    simp only [Fintype.sum_prod_type, u, v]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK ht)).mp
  rw [sq_abs, heq]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  calc
    _ ≤ (∑ w, u w ^ 2) * (∑ w, v w ^ 2) := hc
    _ ≤ (K ^ 2 * tau) * tau := mul_le_mul hu hv
      (Finset.sum_nonneg (fun w _ => sq_nonneg _)) (mul_nonneg (sq_nonneg K) ht)
    _ = (K * tau) ^ 2 := by ring

/-- Two residual entries are bounded pointwise. The other two are summed
as two complete traces using their respective information bijections. -/
theorem four_residual_mass_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo0 : Function.Bijective (fun g => coords g 0))
    (hinfo1 : Function.Bijective (fun g => coords g 1))
    (p epsilon tau : ℝ) (hp : 0 ≤ p) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i y x, |T i y x| ≤ epsilon)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    |∑ g, ZeroFiberResponseEnergy.response T e coords mu g| ≤ p * epsilon ^ 2 * tau := by
  let U (g : G) (x : V) : ℝ := mu x * T 2 (coords g 2) (e 2 x) * T 3 (coords g 3) (e 3 x)
  have hU (g : G) (x : V) : |U g x| ≤ p * epsilon ^ 2 := by
    have he0 : 0 ≤ epsilon := (abs_nonneg (T 2 (coords g 2) (e 2 x))).trans (hentry 2 _ _)
    calc
      _ = |mu x| * |T 2 (coords g 2) (e 2 x)| * |T 3 (coords g 3) (e 3 x)| := by
        dsimp [U]
        rw [abs_mul, abs_mul]
      _ ≤ p * epsilon * epsilon := mul_le_mul
        (mul_le_mul (hmu x) (hentry 2 _ _) (abs_nonneg _) hp)
        (hentry 3 _ _) (abs_nonneg _) (mul_nonneg hp he0)
      _ = _ := by ring
  have h := signed_mass_le_two_traces
    (fun g x => T 0 (coords g 0) (e 0 x))
    (fun g x => T 1 (coords g 1) (e 1 x)) U (p * epsilon ^ 2) tau
    (mul_nonneg hp (sq_nonneg epsilon)) ht hU
    (mixed_trace_le (T 0) (e 0) _ hinfo0 tau (htrace 0))
    (mixed_trace_le (T 1) (e 1) _ hinfo1 tau (htrace 1))
  have heq : (∑ g, ZeroFiberResponseEnergy.response T e coords mu g) =
      ∑ g, ∑ x, U g x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x) := by
    unfold ZeroFiberResponseEnergy.response
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Fin.prod_univ_four, U]
    ring
  rw [heq]
  exact h

/-- Coordinate 0 is bounded constant, 3 a bounded residual entry, and both
residual coordinates 1,2 separately label the same complete fiber. -/
theorem three_residual_constant_mass_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo1 : Function.Bijective (fun g => coords g 1))
    (hinfo2 : Function.Bijective (fun g => coords g 2))
    (p kappa epsilon tau : ℝ) (hp : 0 ≤ p) (hk : 0 ≤ kappa) (he : 0 ≤ epsilon) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hconstant : ∀ y x, |T 0 y x| ≤ kappa)
    (hentry : ∀ y x, |T 3 y x| ≤ epsilon)
    (htrace1 : (∑ y, ∑ x, T 1 y x ^ 2) ≤ tau)
    (htrace2 : (∑ y, ∑ x, T 2 y x ^ 2) ≤ tau) :
    |∑ g, ZeroFiberResponseEnergy.response T e coords mu g| ≤ p * kappa * epsilon * tau := by
  let U (g : G) (x : V) := mu x * T 0 (coords g 0) (e 0 x) * T 3 (coords g 3) (e 3 x)
  have hU (g : G) (x : V) : |U g x| ≤ p * kappa * epsilon := by
    dsimp [U]
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul (hmu x) (hconstant _ _) (abs_nonneg _) hp)
      (hentry _ _) (abs_nonneg _) (mul_nonneg hp hk)
  have h := signed_mass_le_two_traces
    (fun g x => T 1 (coords g 1) (e 1 x))
    (fun g x => T 2 (coords g 2) (e 2 x)) U (p * kappa * epsilon) tau
    (mul_nonneg (mul_nonneg hp hk) he) ht hU
    (mixed_trace_le (T 1) (e 1) _ hinfo1 tau htrace1)
    (mixed_trace_le (T 2) (e 2) _ hinfo2 tau htrace2)
  have heq : (∑ g, ZeroFiberResponseEnergy.response T e coords mu g) =
      ∑ g, ∑ x, U g x * T 1 (coords g 1) (e 1 x) * T 2 (coords g 2) (e 2 x) := by
    unfold ZeroFiberResponseEnergy.response
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Fin.prod_univ_four, U]
    ring
  rw [heq]
  exact h

end AES8.ThreeZeroMass
