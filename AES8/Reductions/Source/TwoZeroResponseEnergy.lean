/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ZeroFiberResponseEnergy
import AES8.Math.PairedFiberEnergy

/-!
# Four-residual common-source energy on a two-coordinate information domain

Cauchy in one signed common source separates response legs 0,1 from 2,3.
One entry cap and one row-energy cap bound the latter factor pointwise.
The literal information bijection onto coordinates 0,1 turns the former
factor into two column energies, bounded by one column cap and one trace.
The result is `p^2 * epsilon^2 * delta^2 * tau`.

Geometry, source-coordinate permutations and all local resources are explicit.
No independence of current coordinates, AES estimate or target projection is
assumed.  Constructive work only; no attacks or predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.TwoZeroResponseEnergy
open AESMixing
open AES8.PairedFiberEnergy (columnEnergy columnEnergy_nonneg permuted_column_sum_le)

section FiniteSums
variable {V G : Type*} [Fintype V] [Fintype G]

theorem sum_pair_of_bijective (coords : G → V × V)
    (hcoords : Function.Bijective coords) (F : V → V → ℝ) :
    (∑ g, F (coords g).1 (coords g).2) = ∑ a, ∑ b, F a b := by
  let e := Equiv.ofBijective coords hcoords
  have h := Equiv.sum_comp e (fun v : V × V => F v.1 v.2)
  simpa only [e, Equiv.ofBijective_apply, Fintype.sum_prod_type] using h

theorem pair_product_energy (f g : V → ℝ) :
    (∑ a, ∑ b, (f a * g b) ^ 2) = (∑ a, f a ^ 2) * (∑ b, g b ^ 2) := by
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

theorem entry_sq_le (T : V → V → ℝ) (epsilon : ℝ)
    (hentry : ∀ y x, |T y x| ≤ epsilon) (y x : V) : T y x ^ 2 ≤ epsilon ^ 2 := by
  simpa only [sq_abs] using
    (pow_le_pow_left₀ (abs_nonneg (T y x)) (hentry y x) 2)

/-- The unweighted two-leg factor uses one entry and one row cap.
The two source-coordinate permutations need not be related. -/
theorem tail_energy_le (A B : V → V → ℝ) (a b : Equiv.Perm V)
    (epsilon delta : ℝ) (hentry : ∀ y x, |B y x| ≤ epsilon)
    (hrow : ∀ y, (∑ x, A y x ^ 2) ≤ delta) (u v : V) :
    (∑ x, (A u (a x) * B v (b x)) ^ 2) ≤ epsilon ^ 2 * delta := by
  calc
    _ = ∑ x, A u (a x) ^ 2 * B v (b x) ^ 2 := by simp only [mul_pow]
    _ ≤ ∑ x, A u (a x) ^ 2 * epsilon ^ 2 :=
      Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (entry_sq_le B epsilon hentry v (b x)) (sq_nonneg _))
    _ = epsilon ^ 2 * ∑ x, A u (a x) ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ = epsilon ^ 2 * ∑ x, A u x ^ 2 := by
      rw [Equiv.sum_comp a (fun x => A u x ^ 2)]
    _ ≤ epsilon ^ 2 * delta := mul_le_mul_of_nonneg_left (hrow u) (sq_nonneg epsilon)

/-- The weighted information-coordinate factor retains one original source
in both legs. Exact coordinate reindexing precedes the column/trace bounds. -/
theorem head_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (p delta tau : ℝ) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    (∑ g, ∑ x,
      (mu x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x)) ^ 2) ≤
      p ^ 2 * delta * tau := by
  have hmu_sq (x : V) : mu x ^ 2 ≤ p ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (mu x)) (hmu x) 2)
  have hpoint (x : V) :
      (∑ g, (mu x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x)) ^ 2) =
        mu x ^ 2 * columnEnergy T 0 (e 0 x) * columnEnergy T 1 (e 1 x) := by
    rw [sum_pair_of_bijective (fun g => (coords g 0, coords g 1)) hinfo
      (fun a b => (mu x * T 0 a (e 0 x) * T 1 b (e 1 x)) ^ 2)]
    have hring (a b : V) : (mu x * T 0 a (e 0 x) * T 1 b (e 1 x)) ^ 2 =
        mu x ^ 2 * (T 0 a (e 0 x) * T 1 b (e 1 x)) ^ 2 := by ring
    simp_rw [hring, ← Finset.mul_sum]
    rw [pair_product_energy]
    unfold columnEnergy
    ring
  calc
    _ = ∑ x, mu x ^ 2 * columnEnergy T 0 (e 0 x) * columnEnergy T 1 (e 1 x) := by
      rw [Finset.sum_comm]
      simp_rw [hpoint]
    _ ≤ ∑ x, p ^ 2 * delta * columnEnergy T 1 (e 1 x) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (columnEnergy_nonneg T 1 (e 1 x))
      exact mul_le_mul (hmu_sq x) (hcolumn 0 (e 0 x))
        (columnEnergy_nonneg T 0 (e 0 x)) (sq_nonneg p)
    _ = (p ^ 2 * delta) * ∑ x, columnEnergy T 1 (e 1 x) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (p ^ 2 * delta) * tau :=
      mul_le_mul_of_nonneg_left (permuted_column_sum_le T e tau htrace 1)
        (mul_nonneg (sq_nonneg p) hd)

end FiniteSums

section Response
variable {V G : Type*} [Fintype V] [Fintype G]

/-- One common signed source labels all four factors. Only the literal
coordinates 0,1 are information coordinates; the other two remain observed. -/
theorem response_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo : Function.Bijective (fun g => (coords g 0, coords g 1)))
    (p epsilon delta tau : ℝ) (hd : 0 ≤ delta)
    (hmu : ∀ x, |mu x| ≤ p)
    (hentry : ∀ i y x, |T i y x| ≤ epsilon)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    (∑ g, ZeroFiberResponseEnergy.response T e coords mu g ^ 2) ≤
      p ^ 2 * epsilon ^ 2 * delta ^ 2 * tau := by
  let A (g : G) : ℝ :=
    ∑ x, (mu x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x)) ^ 2
  let B (g : G) : ℝ :=
    ∑ x, (T 2 (coords g 2) (e 2 x) * T 3 (coords g 3) (e 3 x)) ^ 2
  have hB (g : G) : B g ≤ epsilon ^ 2 * delta :=
    tail_energy_le (T 2) (T 3) (e 2) (e 3) epsilon delta (hentry 3) (hrow 2)
      (coords g 2) (coords g 3)
  have hA : (∑ g, A g) ≤ p ^ 2 * delta * tau :=
    head_energy_le T e coords mu hinfo p delta tau hd hmu hcolumn htrace
  have hpoint (g : G) :
      ZeroFiberResponseEnergy.response T e coords mu g ^ 2 ≤ A g * B g := by
    have heq : ZeroFiberResponseEnergy.response T e coords mu g =
        ∑ x, (mu x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x)) *
          (T 2 (coords g 2) (e 2 x) * T 3 (coords g 3) (e 3 x)) := by
      unfold ZeroFiberResponseEnergy.response
      apply Finset.sum_congr rfl
      intro x _
      simp only [Fin.prod_univ_four]
      ring
    rw [heq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => mu x * T 0 (coords g 0) (e 0 x) * T 1 (coords g 1) (e 1 x))
      (fun x => T 2 (coords g 2) (e 2 x) * T 3 (coords g 3) (e 3 x))
  calc
    _ ≤ ∑ g, A g * B g := Finset.sum_le_sum (fun g _ => hpoint g)
    _ ≤ ∑ g, A g * (epsilon ^ 2 * delta) :=
      Finset.sum_le_sum (fun g _ =>
        mul_le_mul_of_nonneg_left (hB g) (Finset.sum_nonneg (fun x _ => sq_nonneg _)))
    _ = (∑ g, A g) * (epsilon ^ 2 * delta) := (Finset.sum_mul _ _ _).symm
    _ ≤ (p ^ 2 * delta * tau) * (epsilon ^ 2 * delta) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (sq_nonneg epsilon) hd)
    _ = _ := by ring

end Response
end AES8.TwoZeroResponseEnergy
