/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.Gram
import AESMixing.L2Sums

/-!
# A signed common-source energy bound on a one-zero MDS fiber

The finite graph G has two literal information-coordinate systems, (0,2,3)
and (1,2,3). Cauchy--Schwarz splits the eight response legs between these
systems without splitting the common source. A row-energy cap and total
trace control the retained mixed fourth moment; two other legs use column
energies. The resulting bound is p^2 * delta^3 * trace.

The graph's two bijections and local matrix resources are explicit premises.
No AES-specific cap or independence premise is assumed. Constructive proof
work only; no attacks, local execution or manuscript/predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.ZeroFiberResponseEnergy
open AESMixing

section FiniteSums
variable {V G : Type*} [Fintype V] [Fintype G]

theorem sum_triple_of_bijective (coords : G → V × (V × V))
    (hcoords : Function.Bijective coords) (F : V → V → V → ℝ) :
    (∑ g, F (coords g).1 (coords g).2.1 (coords g).2.2) =
      ∑ a, ∑ b, ∑ c, F a b c := by
  let e := Equiv.ofBijective coords hcoords
  have h := Equiv.sum_comp e (fun v : V × (V × V) => F v.1 v.2.1 v.2.2)
  simpa only [e, Equiv.ofBijective_apply, Fintype.sum_prod_type] using h

theorem triple_product_energy (f g h : V → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a * g b * h c) ^ 2) =
      (∑ a, f a ^ 2) * (∑ b, g b ^ 2) * (∑ c, h c ^ 2) := by
  -- Factor from the inner sum outwards, preserving the a,b,c order.
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Source relabeling preserves the complete mixed fourth-moment sum.
Rows, rather than Gram entries, remain after this exact rearrangement. -/
theorem mixed_fourth_sum (A : V → V → ℝ) (e : Equiv.Perm V) :
    (∑ x, ∑ z, ∑ y, (A y (e x) * A y (e z)) ^ 2) =
      ∑ y, (∑ x, A y x ^ 2) ^ 2 := by
  simp only [mul_pow]
  calc
    _ = ∑ x, ∑ y, ∑ z, A y (e x) ^ 2 * A y (e z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, ∑ z, A y (e x) ^ 2 * A y (e z) ^ 2 := Finset.sum_comm
    _ = ∑ y, (∑ x, A y (e x) ^ 2) * (∑ z, A y (e z) ^ 2) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ y, (∑ x, A y x ^ 2) ^ 2 := by
      have hs (y : V) : (∑ x, A y (e x) ^ 2) = ∑ x, A y x ^ 2 :=
        Equiv.sum_comp e (fun x => A y x ^ 2)
      simp_rw [hs]
      simp only [pow_two]

theorem mixed_fourth_sum_le (A : V → V → ℝ) (e : Equiv.Perm V)
    (delta trace : ℝ) (hd : 0 ≤ delta)
    (hrow : ∀ y, (∑ x, A y x ^ 2) ≤ delta)
    (htrace : (∑ y, ∑ x, A y x ^ 2) ≤ trace) :
    (∑ x, ∑ z, ∑ y, (A y (e x) * A y (e z)) ^ 2) ≤ delta * trace := by
  rw [mixed_fourth_sum]
  calc
    _ ≤ ∑ y, delta * ∑ x, A y x ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      simpa only [pow_two] using
        (mul_le_mul_of_nonneg_right (hrow y)
          (Finset.sum_nonneg (fun x _ => sq_nonneg (A y x))))
    _ = delta * ∑ y, ∑ x, A y x ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ delta * trace := mul_le_mul_of_nonneg_left htrace hd

/-- One Cauchy factor uses one information-coordinate system. The tail
source labels may be arbitrary: only their uniform column bounds matter. -/
theorem information_leg_energy_le
    (A B C : V → V → ℝ) (coords : G → V × (V × V))
    (hcoords : Function.Bijective coords) (e : Equiv.Perm V)
    (bLabel cLabel : V → V → V) (weight : V → V → ℝ)
    (p delta trace : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hweight : ∀ x z, |weight x z| ≤ p)
    (hrow : ∀ y, (∑ x, A y x ^ 2) ≤ delta)
    (htrace : (∑ y, ∑ x, A y x ^ 2) ≤ trace)
    (hB : ∀ x, (∑ y, B y x ^ 2) ≤ delta)
    (hC : ∀ x, (∑ y, C y x ^ 2) ≤ delta) :
    (∑ x, ∑ z, ∑ g,
      (weight x z * A (coords g).1 (e x) * A (coords g).1 (e z) *
        B (coords g).2.1 (bLabel x z) * C (coords g).2.2 (cLabel x z)) ^ 2) ≤
      p ^ 2 * delta ^ 3 * trace := by
  have hw (x z : V) : weight x z ^ 2 ≤ p ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (weight x z)) (hweight x z) 2)
  have hpoint (x z : V) :
      (∑ g,
        (weight x z * A (coords g).1 (e x) * A (coords g).1 (e z) *
          B (coords g).2.1 (bLabel x z) * C (coords g).2.2 (cLabel x z)) ^ 2) ≤
        p ^ 2 * delta ^ 2 * ∑ y, (A y (e x) * A y (e z)) ^ 2 := by
    have heq :
        (∑ g,
          (weight x z * A (coords g).1 (e x) * A (coords g).1 (e z) *
            B (coords g).2.1 (bLabel x z) * C (coords g).2.2 (cLabel x z)) ^ 2) =
          weight x z ^ 2 *
            ((∑ y, (A y (e x) * A y (e z)) ^ 2) *
              (∑ y, B y (bLabel x z) ^ 2) * (∑ y, C y (cLabel x z) ^ 2)) := by
      rw [sum_triple_of_bijective coords hcoords (fun a b c =>
        (weight x z * A a (e x) * A a (e z) *
          B b (bLabel x z) * C c (cLabel x z)) ^ 2)]
      have hring (a b c : V) :
          (weight x z * A a (e x) * A a (e z) * B b (bLabel x z) * C c (cLabel x z)) ^ 2 =
            weight x z ^ 2 *
              ((A a (e x) * A a (e z)) * B b (bLabel x z) * C c (cLabel x z)) ^ 2 := by ring
      simp_rw [hring]
      -- The scalar is beneath all three sums; pull it out inside out.
      simp_rw [← Finset.mul_sum]
      rw [triple_product_energy]
    rw [heq]
    have hnonneg : 0 ≤ ∑ y, (A y (e x) * A y (e z)) ^ 2 :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    calc
      _ ≤ p ^ 2 *
          ((∑ y, (A y (e x) * A y (e z)) ^ 2) *
            (∑ y, B y (bLabel x z) ^ 2) * (∑ y, C y (cLabel x z) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hw x z)
          (mul_nonneg (mul_nonneg hnonneg (Finset.sum_nonneg (fun y _ => sq_nonneg _)))
            (Finset.sum_nonneg (fun y _ => sq_nonneg _)))
      _ ≤ p ^ 2 * ((∑ y, (A y (e x) * A y (e z)) ^ 2) * delta * delta) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg p)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hB (bLabel x z)) hnonneg
        · exact hC (cLabel x z)
        · exact Finset.sum_nonneg (fun y _ => sq_nonneg _)
        · exact mul_nonneg hnonneg hd
      _ = _ := by ring
  calc
    _ ≤ ∑ x, ∑ z, p ^ 2 * delta ^ 2 * ∑ y, (A y (e x) * A y (e z)) ^ 2 :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ => hpoint x z))
    _ = (p ^ 2 * delta ^ 2) * ∑ x, ∑ z, ∑ y, (A y (e x) * A y (e z)) ^ 2 := by
      simp only [Finset.mul_sum]
    _ ≤ (p ^ 2 * delta ^ 2) * (delta * trace) :=
      mul_le_mul_of_nonneg_left (mixed_fourth_sum_le A e delta trace hd hrow htrace)
        (mul_nonneg (sq_nonneg p) (sq_nonneg delta))
    _ = _ := by ring

end FiniteSums

section Response
variable {V G : Type*} [Fintype V] [Fintype G]

/-- The actual common source remains a single signed label in all four legs. -/
def response (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ) (g : G) : ℝ :=
  ∑ x, (∏ i : Fin 4, T i (coords g i) (e i x)) * mu x

/-- Two information-coordinate systems suffice for the one-zero response
bound. No tensor-product or independence premise is imposed on the source. -/
theorem response_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : G → Fin 4 → V) (mu : V → ℝ)
    (hinfo0 : Function.Bijective (fun g => (coords g 0, (coords g 2, coords g 3))))
    (hinfo1 : Function.Bijective (fun g => (coords g 1, (coords g 2, coords g 3))))
    (p delta trace : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ trace)
    (hmu : ∀ x, |mu x| ≤ p)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ trace)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta) :
    (∑ g, response T e coords mu g ^ 2) ≤ p ^ 2 * delta ^ 3 * trace := by
  let u : (V × V) × G → ℝ := fun v =>
    mu v.1.1 * T 0 (coords v.2 0) (e 0 v.1.1) * T 0 (coords v.2 0) (e 0 v.1.2) *
      T 2 (coords v.2 2) (e 2 v.1.1) * T 3 (coords v.2 3) (e 3 v.1.2)
  let v : (V × V) × G → ℝ := fun w =>
    mu w.1.2 * T 1 (coords w.2 1) (e 1 w.1.1) * T 1 (coords w.2 1) (e 1 w.1.2) *
      T 2 (coords w.2 2) (e 2 w.1.2) * T 3 (coords w.2 3) (e 3 w.1.1)
  have hu : (∑ w, u w ^ 2) ≤ p ^ 2 * delta ^ 3 * trace := by
    simp only [u, Fintype.sum_prod_type]
    exact information_leg_energy_le (T 0) (T 2) (T 3)
      (fun g => (coords g 0, (coords g 2, coords g 3))) hinfo0 (e 0)
      (fun x _ => e 2 x) (fun _ z => e 3 z) (fun x _ => mu x)
      p delta trace hp hd (fun x _ => hmu x) (hrow 0) (htrace 0) (hcolumn 2) (hcolumn 3)
  have hv : (∑ w, v w ^ 2) ≤ p ^ 2 * delta ^ 3 * trace := by
    simp only [v, Fintype.sum_prod_type]
    exact information_leg_energy_le (T 1) (T 2) (T 3)
      (fun g => (coords g 1, (coords g 2, coords g 3))) hinfo1 (e 1)
      (fun _ z => e 2 z) (fun x _ => e 3 x) (fun _ z => mu z)
      p delta trace hp hd (fun _ z => hmu z) (hrow 1) (htrace 1) (hcolumn 2) (hcolumn 3)
  have heq : (∑ g, response T e coords mu g ^ 2) = ∑ w, u w * v w := by
    have h := gram_quadratic
      (fun g x => ∏ i : Fin 4, T i (coords g i) (e i x)) mu
    rw [show (∑ g, response T e coords mu g ^ 2) =
      ∑ g, (∑ x, (∏ i : Fin 4, T i (coords g i) (e i x)) * mu x) ^ 2 by rfl, h]
    simp only [gram, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro g _
    simp only [u, v, Fin.prod_univ_four]
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hnonneg : 0 ≤ p ^ 2 * delta ^ 3 * trace :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (pow_nonneg hd 3)) ht
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun g _ => sq_nonneg _)) hnonneg).mp
  rw [heq]
  exact hc.trans (by
    simpa only [pow_two] using
      (mul_le_mul hu hv (Finset.sum_nonneg (fun w _ => sq_nonneg (v w))) hnonneg))

end Response
end AES8.ZeroFiberResponseEnergy
