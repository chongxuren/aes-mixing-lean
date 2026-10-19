import Mathlib.Analysis.MeanInequalities

/-!
# Five-factor finite Holder with one common fifth-moment cap

Equal-weight AM-GM applied to the fifth powers proves the common-cap
consequence of Holder directly. All sums use counting measure; there is
no alphabet-size average and no normalization of a zero moment.

Constructive mathematics only; no attacks, numerical workloads,
manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FifthMomentHolder

theorem prod_le_fifth_average (a : Fin 5 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i : Fin 5, a i) ≤ (1 / 5 : ℝ) * ∑ i : Fin 5, a i ^ 5 := by
  have h := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin 5)) (fun _ => (5 : ℝ)⁻¹) (fun i => a i ^ 5)
    (by intro i _; norm_num) (by norm_num) (by intro i _; exact pow_nonneg (ha i) 5)
  have hroot (i : Fin 5) : (a i ^ 5) ^ ((5 : ℝ)⁻¹) = a i :=
    Real.pow_rpow_inv_natCast (ha i) (by decide : (5 : ℕ) ≠ 0)
  simpa only [hroot, ← Finset.mul_sum, one_div] using h

/-- Raw finite Holder in the equal fifth-moment-cap form used by the
five physical coordinates of an MDS section. -/
theorem sum_prod_le_common_fifth {X : Type*} [Fintype X]
    (f : Fin 5 → X → ℝ) (hf : ∀ i x, 0 ≤ f i x) (H : ℝ)
    (hmoment : ∀ i, (∑ x : X, f i x ^ 5) ≤ H) :
    (∑ x : X, ∏ i : Fin 5, f i x) ≤ H := by
  calc
    _ ≤ ∑ x : X, (1 / 5 : ℝ) * ∑ i : Fin 5, f i x ^ 5 :=
      Finset.sum_le_sum (fun x _ => prod_le_fifth_average (fun i => f i x) (fun i => hf i x))
    _ = (1 / 5 : ℝ) * ∑ i : Fin 5, ∑ x : X, f i x ^ 5 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (1 / 5 : ℝ) * ∑ _i : Fin 5, H :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hmoment i)) (by norm_num)
    _ = H := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Separate bijections may reparametrize the five factors. They all use
the same raw source, without an independence premise. -/
theorem sum_prod_bijective_le {X V : Type*} [Fintype X] [Fintype V]
    (e : Fin 5 → X ≃ V) (g : Fin 5 → V → ℝ) (hg : ∀ i v, 0 ≤ g i v) (H : ℝ)
    (hmoment : ∀ i, (∑ v : V, g i v ^ 5) ≤ H) :
    (∑ x : X, ∏ i : Fin 5, g i (e i x)) ≤ H := by
  apply sum_prod_le_common_fifth (fun i x => g i (e i x)) (fun i x => hg i (e i x)) H
  intro i
  calc
    _ = ∑ v : V, g i v ^ 5 := (e i).sum_comp (fun v => g i v ^ 5)
    _ ≤ H := hmoment i

end AESConcrete.FifthMomentHolder
