/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.TwoZeroResponseEnergy

/-!
# Common-source response energy on a one-coordinate information domain

Four residual legs give p^2 * epsilon^4 * delta * tau. Three residual
legs and one bounded constant leg give p^2 * kappa^2 * epsilon^2 * delta * tau.
All source labels stay common, and all source-coordinate permutations remain
arbitrary. Geometry and AES constants are separate consumers.  No local execution or proof bypass.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ThreeZeroResponseEnergy
open AESMixing
variable {V G : Type*} [Fintype V] [Fintype G]

theorem sum_of_bijective (coords : G → V) (hcoords : Function.Bijective coords)
    (f : V → ℝ) : (∑ g, f (coords g)) = ∑ y, f y :=
  (Equiv.ofBijective coords hcoords).sum_comp f

theorem row_sum_relabel (T : V → V → ℝ) (e : Equiv.Perm V) (y : V) :
    (∑ x, T y (e x) ^ 2) = ∑ x, T y x ^ 2 :=
  Equiv.sum_comp e (fun x => T y x ^ 2)

theorem trace_information_le (T : V → V → ℝ) (e : Equiv.Perm V)
    (coords : G → V) (hinfo : Function.Bijective coords) (tau : ℝ)
    (htrace : (∑ y, ∑ x, T y x ^ 2) ≤ tau) :
    (∑ g, ∑ x, T (coords g) (e x) ^ 2) ≤ tau := by
  simp_rw [row_sum_relabel]
  rw [sum_of_bijective coords hinfo (fun y => ∑ x, T y x ^ 2)]
  exact htrace

/-- One weighted information leg and three tail legs; two tail entries
are bounded before the remaining ordinary row energy is summed. -/
theorem four_residual_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo : Function.Bijective (fun g => coords g 0))
    (p epsilon delta tau : ℝ) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i y x, |T i y x| ≤ epsilon)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (htrace : (∑ y, ∑ x, T 0 y x ^ 2) ≤ tau) :
    (∑ g, ZeroFiberResponseEnergy.response T e coords mu g ^ 2) ≤
      p ^ 2 * epsilon ^ 4 * delta * tau := by
  let A (g : G) : ℝ := ∑ x, (mu x * T 0 (coords g 0) (e 0 x)) ^ 2
  let B (g : G) : ℝ := ∑ x,
    (T 1 (coords g 1) (e 1 x) * T 2 (coords g 2) (e 2 x) *
      T 3 (coords g 3) (e 3 x)) ^ 2
  have hB (g : G) : B g ≤ epsilon ^ 4 * delta := by
    have hpoint (x : V) :
        (T 1 (coords g 1) (e 1 x) * T 2 (coords g 2) (e 2 x) *
          T 3 (coords g 3) (e 3 x)) ^ 2 ≤
        T 1 (coords g 1) (e 1 x) ^ 2 * (epsilon ^ 2 * epsilon ^ 2) := by
      calc
        _ = T 1 (coords g 1) (e 1 x) ^ 2 *
            (T 2 (coords g 2) (e 2 x) ^ 2 * T 3 (coords g 3) (e 3 x) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul
            (TwoZeroResponseEnergy.entry_sq_le (T 2) epsilon (hentry 2) _ _)
            (TwoZeroResponseEnergy.entry_sq_le (T 3) epsilon (hentry 3) _ _)
            (sq_nonneg _) (sq_nonneg epsilon)) (sq_nonneg _)
    calc
      _ ≤ ∑ x, T 1 (coords g 1) (e 1 x) ^ 2 * (epsilon ^ 2 * epsilon ^ 2) :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ x, T 1 (coords g 1) x ^ 2) * epsilon ^ 4 := by
        rw [← Finset.sum_mul, row_sum_relabel]
        ring
      _ ≤ delta * epsilon ^ 4 := mul_le_mul_of_nonneg_right (hrow 1 _) (by positivity)
      _ = _ := mul_comm _ _
  have hA : (∑ g, A g) ≤ p ^ 2 * tau := by
    have hpoint (g : G) (x : V) :
        (mu x * T 0 (coords g 0) (e 0 x)) ^ 2 ≤
          p ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (mu x)) (hmu x) 2)
    calc
      _ ≤ ∑ g, ∑ x, p ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 :=
        Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun x _ => hpoint g x))
      _ = p ^ 2 * ∑ g, ∑ x, T 0 (coords g 0) (e 0 x) ^ 2 := by
        simp only [← Finset.mul_sum]
      _ ≤ p ^ 2 * tau := mul_le_mul_of_nonneg_left
        (trace_information_le (T 0) (e 0) (fun g => coords g 0) hinfo tau htrace) (sq_nonneg p)
  have hpoint (g : G) :
      ZeroFiberResponseEnergy.response T e coords mu g ^ 2 ≤ A g * B g := by
    have heq : ZeroFiberResponseEnergy.response T e coords mu g =
        ∑ x, (mu x * T 0 (coords g 0) (e 0 x)) *
          (T 1 (coords g 1) (e 1 x) * T 2 (coords g 2) (e 2 x) *
            T 3 (coords g 3) (e 3 x)) := by
      unfold ZeroFiberResponseEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      simp only [Fin.prod_univ_four]
      ring
    rw [heq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  calc
    _ ≤ ∑ g, A g * B g := Finset.sum_le_sum (fun g _ => hpoint g)
    _ ≤ ∑ g, A g * (epsilon ^ 4 * delta) := Finset.sum_le_sum
      (fun g _ => mul_le_mul_of_nonneg_left (hB g) (Finset.sum_nonneg (fun x _ => sq_nonneg _)))
    _ = (∑ g, A g) * (epsilon ^ 4 * delta) := (Finset.sum_mul _ _ _).symm
    _ ≤ (p ^ 2 * tau) * (epsilon ^ 4 * delta) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (by positivity) hd)
    _ = _ := by ring

/-- Coordinate 0 is bounded constant, 3 a bounded residual entry, 1 the
information residual leg and 2 the row residual leg. No product law appears. -/
theorem three_residual_constant_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo : Function.Bijective (fun g => coords g 1))
    (p kappa epsilon delta tau : ℝ) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hconstant : ∀ y x, |T 0 y x| ≤ kappa)
    (hentry : ∀ y x, |T 3 y x| ≤ epsilon)
    (hrow : ∀ y, (∑ x, T 2 y x ^ 2) ≤ delta)
    (htrace : (∑ y, ∑ x, T 1 y x ^ 2) ≤ tau) :
    (∑ g, ZeroFiberResponseEnergy.response T e coords mu g ^ 2) ≤
      p ^ 2 * kappa ^ 2 * epsilon ^ 2 * delta * tau := by
  let K : ℝ := p ^ 2 * kappa ^ 2 * epsilon ^ 2
  let A (g : G) : ℝ := ∑ x, T 1 (coords g 1) (e 1 x) ^ 2
  let B (g : G) : ℝ := ∑ x, T 2 (coords g 2) (e 2 x) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (g : G) :
      ZeroFiberResponseEnergy.response T e coords mu g ^ 2 ≤ K * (A g * B g) := by
    let u (x : V) := mu x * T 0 (coords g 0) (e 0 x) *
      T 3 (coords g 3) (e 3 x) * T 1 (coords g 1) (e 1 x)
    let v (x : V) := T 2 (coords g 2) (e 2 x)
    have hu (x : V) : u x ^ 2 ≤ K * T 1 (coords g 1) (e 1 x) ^ 2 := by
      have hm : mu x ^ 2 ≤ p ^ 2 := by
        simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (mu x)) (hmu x) 2)
      have hc := TwoZeroResponseEnergy.entry_sq_le (T 0) kappa hconstant (coords g 0) (e 0 x)
      have he := TwoZeroResponseEnergy.entry_sq_le (T 3) epsilon hentry (coords g 3) (e 3 x)
      have hp : mu x ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 *
          T 3 (coords g 3) (e 3 x) ^ 2 ≤ K :=
        mul_le_mul (mul_le_mul hm hc (sq_nonneg _) (sq_nonneg p)) he
          (sq_nonneg _) (mul_nonneg (sq_nonneg p) (sq_nonneg kappa))
      calc
        _ = (mu x ^ 2 * T 0 (coords g 0) (e 0 x) ^ 2 *
            T 3 (coords g 3) (e 3 x) ^ 2) * T 1 (coords g 1) (e 1 x) ^ 2 := by dsimp [u]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    have hsum : (∑ x, u x ^ 2) ≤ K * A g := by
      calc
        _ ≤ ∑ x, K * T 1 (coords g 1) (e 1 x) ^ 2 := Finset.sum_le_sum (fun x _ => hu x)
        _ = _ := (Finset.mul_sum _ _ _).symm
    have heq : ZeroFiberResponseEnergy.response T e coords mu g = ∑ x, u x * v x := by
      unfold ZeroFiberResponseEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      simp only [u, v, Fin.prod_univ_four]
      ring
    rw [heq]
    calc
      _ ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
      _ ≤ (K * A g) * B g :=
        mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg (fun x _ => sq_nonneg _))
      _ = _ := by ring
  have hA : (∑ g, A g) ≤ tau :=
    trace_information_le (T 1) (e 1) (fun g => coords g 1) hinfo tau htrace
  have hB (g : G) : B g ≤ delta := by
    dsimp [B]
    rw [row_sum_relabel]
    exact hrow _
  calc
    _ ≤ ∑ g, K * (A g * B g) := Finset.sum_le_sum (fun g _ => hpoint g)
    _ ≤ ∑ g, K * (A g * delta) := Finset.sum_le_sum (fun g _ =>
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hB g) (Finset.sum_nonneg (fun x _ => sq_nonneg _))) hK)
    _ = (K * delta) * ∑ g, A g := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
    _ ≤ (K * delta) * tau := mul_le_mul_of_nonneg_left hA (mul_nonneg hK hd)
    _ = _ := by dsimp [K] <;> ring

end AES8.ThreeZeroResponseEnergy
