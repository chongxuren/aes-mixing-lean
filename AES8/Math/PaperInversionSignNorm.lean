import AESMixing.CharacterGram
import AESMixing.L2Sums

/-! The arbitrary-cardinality sign-Gram route to inversion contraction.
The exact difference-count identity is deliberately a separate hypothesis.
This generalizes the inherited cardinality-256 analytic calculation without
assuming a finite-field trace formula or histogram. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionSignNorm
open AESMixing
set_option autoImplicit false
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sign_gram_energy (q : ℝ) (H : I → I → ℝ)
    (hH : ∀ i j, gram H i j = (if i = j then q else 0) - 1)
    (x : I → ℝ) :
    (∑ y, (∑ i, H y i*x i)^2) = q*(∑ i, x i^2) - (∑ i, x i)^2 := by
  rw [gram_quadratic]
  simp_rw [hH, mul_sub, mul_one, Finset.sum_sub_distrib]
  have hd : (∑ i, ∑ j, x i*x j*(if i=j then q else 0)) = q*∑ i, x i^2 := by
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd, ← Finset.sum_mul_sum, pow_two]

theorem sign_l2 (q : ℝ) (hq : 0 ≤ q) (H : I → I → ℝ)
    (hH : ∀ i j, gram H i j = (if i = j then q else 0) - 1)
    (x : I → ℝ) (hx : ∑ i, x i = 0) :
    l2 (fun y => ∑ i, H y i*x i) = Real.sqrt q*l2 x := by
  unfold l2
  rw [sign_gram_energy q H hH, hx, sq, zero_mul, sub_zero, Real.sqrt_mul hq]

/-- Generic contraction after the constant direction is removed. -/
theorem residual_l2 (q : ℝ) (hq : 0 < q) (D H : I → I → ℝ)
    (e : Equiv.Perm I)
    (hH : ∀ i j, gram H i j = (if i = j then q else 0)-1)
    (hD : ∀ y i, D y i = (1+H y i+2*(if e y=i then (1 : ℝ) else 0))/q)
    (x : I → ℝ) (hx : ∑ i, x i = 0) :
    l2 (fun y => ∑ i, D y i*x i) ≤ (Real.sqrt q+2)/q*l2 x := by
  have hact (y : I) : (∑ i, D y i*x i) =
      q⁻¹*((∑ i, H y i*x i)+2*x (e y)) := by
    have ht (i : I) : D y i*x i =
        (x i+H y i*x i+2*(if e y=i then x i else 0))/q := by
      rw [hD]
      split_ifs <;> ring
    simp_rw [ht]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx]
    simp
    ring
  have hp : l2 (fun y => x (e y)) = l2 x := by
    unfold l2
    congr 1
    exact Equiv.sum_comp e (fun i => x i^2)
  calc
    _ = q⁻¹*l2 (fun y => (∑ i, H y i*x i)+2*x (e y)) := by
      simp_rw [hact]
      rw [l2_scale, abs_of_pos (inv_pos.mpr hq)]
    _ ≤ q⁻¹*(l2 (fun y => ∑ i, H y i*x i)+2*l2 x) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      have h := l2_add_le (fun y => ∑ i, H y i*x i) (fun y => 2*x (e y))
      rw [l2_scale, hp, abs_of_pos (by norm_num : (0 : ℝ)<2)] at h
      exact h
    _ = _ := by rw [sign_l2 q hq.le H hH x hx]; ring

end AES8.PaperInversionSignNorm
