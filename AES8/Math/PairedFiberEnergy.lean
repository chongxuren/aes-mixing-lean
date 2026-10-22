/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.Gram
import AESMixing.L2Sums

/-!
# Signed common-source Cauchy on a restricted paired fiber

Two literal mixed-coordinate maps of the full paired domain H are bijective:
(left0,right1,right2,right3) and (right0,left1,left2,left3). The event remains
inside the signed cross sum. Cauchy splits its eight channel legs into two
four-leg factors; only their nonnegative squared sums are enlarged to H.
Column energies and total entry-square traces then give p^2 * delta^2 * tau^2.

The same original x and z label their four respective channel legs. Arbitrary
source-coordinate permutations, including affine translations, are allowed.
No product source, row-energy cap, diffusion geometry, numerical AES estimate,
activity-projection normalization, or mixing conclusion is assumed here.

-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.PairedFiberEnergy
open AESMixing

section FiniteSums
variable {V H : Type*} [Fintype V] [Fintype H]

abbrev Quad (V : Type*) := V × (V × (V × V))

theorem sum_quad_of_bijective (coords : H → Quad V)
    (hcoords : Function.Bijective coords) (F : V → V → V → V → ℝ) :
    (∑ h, F (coords h).1 (coords h).2.1 (coords h).2.2.1 (coords h).2.2.2) =
      ∑ a, ∑ b, ∑ c, ∑ d, F a b c d := by
  let e := Equiv.ofBijective coords hcoords
  have he := Equiv.sum_comp e
    (fun v : Quad V => F v.1 v.2.1 v.2.2.1 v.2.2.2)
  simpa only [e, Equiv.ofBijective_apply, Fintype.sum_prod_type] using he

theorem quad_product_energy (f g h j : V → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a * g b * h c * j d) ^ 2) =
      (∑ a, f a ^ 2) * (∑ b, g b ^ 2) * (∑ c, h c ^ 2) * (∑ d, j d ^ 2) := by
  -- Factor from the innermost sum, preserving coordinate order.
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

def columnEnergy (T : Fin 4 → V → V → ℝ) (i : Fin 4) (x : V) : ℝ :=
  ∑ y, T i y x ^ 2

theorem columnEnergy_nonneg (T : Fin 4 → V → V → ℝ) (i : Fin 4) (x : V) :
    0 ≤ columnEnergy T i x :=
  Finset.sum_nonneg (fun y _ => sq_nonneg _)

theorem permuted_column_sum_le (T : Fin 4 → V → V → ℝ)
    (e : Fin 4 → Equiv.Perm V) (tau : ℝ)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) (i : Fin 4) :
    (∑ x, columnEnergy T i (e i x)) ≤ tau := by
  calc
    _ = ∑ x, columnEnergy T i x := Equiv.sum_comp (e i) (columnEnergy T i)
    _ = ∑ y, ∑ x, T i y x ^ 2 := by
      unfold columnEnergy
      rw [Finset.sum_comm]
    _ ≤ tau := htrace i

/-- One squared Cauchy factor, on the full information-coordinate domain.
The isolated leg uses source x; all three other legs use the same source z. -/
theorem information_energy_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (coords : H → Quad V) (hcoords : Function.Bijective coords)
    (mu : V → ℝ) (p delta tau : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, columnEnergy T i x ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    (∑ x, ∑ z, ∑ h,
      (mu x * T 0 (coords h).1 (e 0 x) * T 1 (coords h).2.1 (e 1 z) *
        T 2 (coords h).2.2.1 (e 2 z) * T 3 (coords h).2.2.2 (e 3 z)) ^ 2) ≤
      p ^ 2 * delta ^ 2 * tau ^ 2 := by
  have hmu_sq (x : V) : mu x ^ 2 ≤ p ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (mu x)) (hmu x) 2)
  have hpoint (x z : V) :
      (∑ h,
        (mu x * T 0 (coords h).1 (e 0 x) * T 1 (coords h).2.1 (e 1 z) *
          T 2 (coords h).2.2.1 (e 2 z) * T 3 (coords h).2.2.2 (e 3 z)) ^ 2) =
        (mu x ^ 2 * columnEnergy T 0 (e 0 x)) *
          (columnEnergy T 1 (e 1 z) * columnEnergy T 2 (e 2 z) *
            columnEnergy T 3 (e 3 z)) := by
    rw [sum_quad_of_bijective coords hcoords (fun a b c d =>
      (mu x * T 0 a (e 0 x) * T 1 b (e 1 z) *
        T 2 c (e 2 z) * T 3 d (e 3 z)) ^ 2)]
    have hring (a b c d : V) :
        (mu x * T 0 a (e 0 x) * T 1 b (e 1 z) * T 2 c (e 2 z) *
          T 3 d (e 3 z)) ^ 2 =
          mu x ^ 2 *
            (T 0 a (e 0 x) * T 1 b (e 1 z) * T 2 c (e 2 z) *
              T 3 d (e 3 z)) ^ 2 := by ring
    simp_rw [hring, ← Finset.mul_sum]
    rw [quad_product_energy]
    unfold columnEnergy
    ring
  have hsingle :
      (∑ x, mu x ^ 2 * columnEnergy T 0 (e 0 x)) ≤ p ^ 2 * tau := by
    calc
      _ ≤ ∑ x, p ^ 2 * columnEnergy T 0 (e 0 x) :=
        Finset.sum_le_sum (fun x _ =>
          mul_le_mul_of_nonneg_right (hmu_sq x) (columnEnergy_nonneg T 0 (e 0 x)))
      _ = p ^ 2 * ∑ x, columnEnergy T 0 (e 0 x) := (Finset.mul_sum _ _ _).symm
      _ ≤ p ^ 2 * tau :=
        mul_le_mul_of_nonneg_left (permuted_column_sum_le T e tau htrace 0) (sq_nonneg p)
  have htail_point (z : V) :
      columnEnergy T 1 (e 1 z) * columnEnergy T 2 (e 2 z) *
        columnEnergy T 3 (e 3 z) ≤ delta ^ 2 * columnEnergy T 1 (e 1 z) := by
    calc
      _ ≤ columnEnergy T 1 (e 1 z) * delta * delta := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hcolumn 2 (e 2 z))
            (columnEnergy_nonneg T 1 (e 1 z))
        · exact hcolumn 3 (e 3 z)
        · exact columnEnergy_nonneg T 3 (e 3 z)
        · exact mul_nonneg (columnEnergy_nonneg T 1 (e 1 z)) hd
      _ = _ := by ring
  have htail :
      (∑ z, columnEnergy T 1 (e 1 z) * columnEnergy T 2 (e 2 z) *
        columnEnergy T 3 (e 3 z)) ≤ delta ^ 2 * tau := by
    calc
      _ ≤ ∑ z, delta ^ 2 * columnEnergy T 1 (e 1 z) :=
        Finset.sum_le_sum (fun z _ => htail_point z)
      _ = delta ^ 2 * ∑ z, columnEnergy T 1 (e 1 z) := (Finset.mul_sum _ _ _).symm
      _ ≤ delta ^ 2 * tau :=
        mul_le_mul_of_nonneg_left (permuted_column_sum_le T e tau htrace 1)
          (sq_nonneg delta)
  calc
    _ = (∑ x, mu x ^ 2 * columnEnergy T 0 (e 0 x)) *
        (∑ z, columnEnergy T 1 (e 1 z) * columnEnergy T 2 (e 2 z) *
          columnEnergy T 3 (e 3 z)) := by
      simp_rw [hpoint]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ (p ^ 2 * tau) * (delta ^ 2 * tau) :=
      mul_le_mul hsingle htail
        (Finset.sum_nonneg (fun z _ => mul_nonneg
          (mul_nonneg (columnEnergy_nonneg T 1 (e 1 z))
            (columnEnergy_nonneg T 2 (e 2 z))) (columnEnergy_nonneg T 3 (e 3 z))))
        (mul_nonneg (sq_nonneg p) ht)
    _ = _ := by ring

theorem restricted_square_le (allowed : Prop) [Decidable allowed] (a : ℝ) :
    (if allowed then a else 0) ^ 2 ≤ a ^ 2 := by
  by_cases ha : allowed
  · rw [if_pos ha]
  · rw [if_neg ha, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg a

end FiniteSums

section RestrictedCross
variable {V H : Type*} [Fintype V] [Fintype H]

/-- Both source labels and all eight channel legs remain literal.
The allowed predicate can impose the two nonzero activity endpoints. -/
def restrictedCross (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (left right : H → Fin 4 → V) (allowed : H → Prop) [DecidablePred allowed]
    (mu : V → ℝ) : ℝ :=
  ∑ x, ∑ z, ∑ h, if allowed h then mu x * mu z *
    ∏ i : Fin 4, T i (left h i) (e i x) * T i (right h i) (e i z) else 0

/-- Cauchy is applied before removing a single event restriction. The two
full-domain information bijections are the only geometry premises. -/
theorem abs_restrictedCross_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (left right : H → Fin 4 → V) (allowed : H → Prop) [DecidablePred allowed]
    (mu : V → ℝ)
    (hleft : Function.Bijective
      (fun h => (left h 0, (right h 1, (right h 2, right h 3)))))
    (hright : Function.Bijective
      (fun h => (right h 0, (left h 1, (left h 2, left h 3)))))
    (p delta tau : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    |restrictedCross T e left right allowed mu| ≤ p ^ 2 * delta ^ 2 * tau ^ 2 := by
  let legL (x z : V) (h : H) : ℝ :=
    mu x * T 0 (left h 0) (e 0 x) * T 1 (right h 1) (e 1 z) *
      T 2 (right h 2) (e 2 z) * T 3 (right h 3) (e 3 z)
  let legR (x z : V) (h : H) : ℝ :=
    mu z * T 0 (right h 0) (e 0 z) * T 1 (left h 1) (e 1 x) *
      T 2 (left h 2) (e 2 x) * T 3 (left h 3) (e 3 x)
  let u : (V × V) × H → ℝ := fun w =>
    if allowed w.2 then legL w.1.1 w.1.2 w.2 else 0
  let v : (V × V) × H → ℝ := fun w =>
    if allowed w.2 then legR w.1.1 w.1.2 w.2 else 0
  have hL : (∑ x, ∑ z, ∑ h, legL x z h ^ 2) ≤ p ^ 2 * delta ^ 2 * tau ^ 2 :=
    information_energy_le T e
      (fun h => (left h 0, (right h 1, (right h 2, right h 3)))) hleft
      mu p delta tau hp hd ht hmu hcolumn htrace
  have hR : (∑ x, ∑ z, ∑ h, legR x z h ^ 2) ≤ p ^ 2 * delta ^ 2 * tau ^ 2 := by
    rw [Finset.sum_comm]
    exact information_energy_le T e
      (fun h => (right h 0, (left h 1, (left h 2, left h 3)))) hright
      mu p delta tau hp hd ht hmu hcolumn htrace
  have hu : (∑ w, u w ^ 2) ≤ p ^ 2 * delta ^ 2 * tau ^ 2 := by
    simp only [u, Fintype.sum_prod_type]
    exact (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ =>
      Finset.sum_le_sum (fun h _ => restricted_square_le (allowed h) (legL x z h))))).trans hL
  have hv : (∑ w, v w ^ 2) ≤ p ^ 2 * delta ^ 2 * tau ^ 2 := by
    simp only [v, Fintype.sum_prod_type]
    exact (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ =>
      Finset.sum_le_sum (fun h _ => restricted_square_le (allowed h) (legR x z h))))).trans hR
  have heq : restrictedCross T e left right allowed mu = ∑ w, u w * v w := by
    simp only [restrictedCross, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : allowed h
    · simp only [u, v, hh, if_true, legL, legR, Fin.prod_univ_four]
      ring
    · simp only [u, v, hh, if_false, zero_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hnonneg : 0 ≤ p ^ 2 * delta ^ 2 * tau ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg p) (sq_nonneg delta)) (sq_nonneg tau)
  apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
  rw [sq_abs, heq]
  exact hc.trans (by
    simpa only [pow_two] using
      (mul_le_mul hu hv (Finset.sum_nonneg (fun w _ => sq_nonneg (v w))) hnonneg))

/-- Direct upper-bound form for the literal restricted common-source sum. -/
theorem restrictedCross_le
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (left right : H → Fin 4 → V) (allowed : H → Prop) [DecidablePred allowed]
    (mu : V → ℝ)
    (hleft : Function.Bijective
      (fun h => (left h 0, (right h 1, (right h 2, right h 3)))))
    (hright : Function.Bijective
      (fun h => (right h 0, (left h 1, (left h 2, left h 3)))))
    (p delta tau : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    restrictedCross T e left right allowed mu ≤ p ^ 2 * delta ^ 2 * tau ^ 2 :=
  (le_abs_self _).trans
    (abs_restrictedCross_le T e left right allowed mu hleft hright p delta tau
      hp hd ht hmu hcolumn htrace)

end RestrictedCross
end AES8.PairedFiberEnergy
