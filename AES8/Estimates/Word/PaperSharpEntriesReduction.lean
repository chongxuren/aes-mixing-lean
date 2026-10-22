import AESConcrete.MDSFiveFactorEntry
import AESConcrete.ByteFifthMoments

/-!
# Pair-moment reduction for physical five-factor sections

Draft only; no Lean execution has been performed. This module proves a reusable
analytic reduction, not the paper's concrete 14/q or 27/q entry resource.
The mixed byte pair moments retain the AES affine/dual map and remain the
missing semantic certificate. No target entry cap is an assumption here.
Constructive proof work only; no attacks or numerical search.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesReduction

set_option autoImplicit false

/-- Equal-weight AM-GM for any nonempty finite family. -/
theorem prod_le_power_average {I : Type*} [Fintype I]
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hI : 0 < Fintype.card I) :
    (∏ i, a i) ≤ (Fintype.card I : ℝ)⁻¹ *
      ∑ i, a i ^ Fintype.card I := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hI)
  have hw : (∑ _ : I, (Fintype.card I : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  have h := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset I) (fun _ => (Fintype.card I : ℝ)⁻¹)
    (fun i => a i ^ Fintype.card I)
    (by intro i _; positivity) hw
    (by intro i _; exact pow_nonneg (ha i) _)
  have hroot (i : I) :
      (a i ^ Fintype.card I) ^ ((Fintype.card I : ℝ)⁻¹) = a i :=
    Real.pow_rpow_inv_natCast (ha i) (Nat.ne_of_gt hI)
  simpa only [hroot, ← Finset.mul_sum] using h

/-- Split a section into two nonempty coordinate sides. The product bound is
an average of two-leg moments. It keeps the relation between opposite-side
physical coordinates instead of replacing it by separate fifth moments. -/
theorem sum_prod_le_pair_moment
    {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]
    (f : I → X → ℝ) (g : J → X → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hg : ∀ j x, 0 ≤ g j x)
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J) (H : ℝ)
    (hpair : ∀ i j,
      (∑ x, f i x ^ Fintype.card I * g j x ^ Fintype.card J) ≤ H) :
    (∑ x, (∏ i, f i x) * ∏ j, g j x) ≤ H := by
  let u : ℝ := (Fintype.card I : ℝ)⁻¹
  let v : ℝ := (Fintype.card J : ℝ)⁻¹
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcI : (Fintype.card I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hI)
  have hcJ : (Fintype.card J : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hJ)
  have hpoint (x : X) :
      (∏ i, f i x) * (∏ j, g j x) ≤
        u * v * ∑ i, ∑ j,
          f i x ^ Fintype.card I * g j x ^ Fintype.card J := by
    have he := mul_le_mul
      (prod_le_power_average (fun i => f i x) (fun i => hf i x) hI)
      (prod_le_power_average (fun j => g j x) (fun j => hg j x) hJ)
      (Finset.prod_nonneg (fun j _ => hg j x))
      (mul_nonneg hu (Finset.sum_nonneg (fun i _ => pow_nonneg (hf i x) _)))
    calc
      _ ≤ (u * ∑ i, f i x ^ Fintype.card I) *
          (v * ∑ j, g j x ^ Fintype.card J) := he
      _ = _ := by
        rw [← Finset.sum_mul_sum]
        ring
  calc
    _ ≤ ∑ x, u * v * ∑ i, ∑ j,
        f i x ^ Fintype.card I * g j x ^ Fintype.card J :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = u * v * ∑ i, ∑ j, ∑ x,
        f i x ^ Fintype.card I * g j x ^ Fintype.card J := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ u * v * ∑ _i : I, ∑ _j : J, H :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j)))
        (mul_nonneg hu hv)
    _ = H := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [u, v]
      field_simp [hcI, hcJ] <;> ring

/-- Same estimate in the sum-type labeling of a physical section. -/
theorem sum_prod_sum_type_le_pair_moment
    {I J X : Type*} [Fintype I] [Fintype J] [Fintype X]
    (T : I ⊕ J → X → ℝ) (hT : ∀ p x, 0 ≤ T p x)
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J) (H : ℝ)
    (hpair : ∀ i j,
      (∑ x, T (Sum.inl i) x ^ Fintype.card I *
        T (Sum.inr j) x ^ Fintype.card J) ≤ H) :
    (∑ x, ∏ p : I ⊕ J, T p x) ≤ H := by
  simp only [Fintype.prod_sum_type]
  exact sum_prod_le_pair_moment
    (fun i x => T (Sum.inl i) x) (fun j x => T (Sum.inr j) x)
    (fun i x => hT _ x) (fun j x => hT _ x) hI hJ H hpair

end AES8.PaperSharpEntriesReduction
