import AES8.Math.PaperCharacterBasis

/-! Anti-convolution is diagonal up to character inversion, and a scalar
bound on the nonconstant multipliers bounds its mean-zero operator norm.
No Gauss-sum algebra is repeated in this leaf. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open WithLp
namespace AES8.PaperCharacterOperator
open PaperCharacterBasis
set_option autoImplicit false
variable {A : Type*} [AddCommGroup A] [Fintype A]

def multiplier (k : A → ℂ) (χ : Character A) : ℂ := ∑ a, k a * χ a

def operator (k : A → ℂ) : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ A where
  toFun f := toLp 2 (fun b => ∑ a, k (b + a) * f a)
  map_add' f g := by ext b; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext b; simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem operator_apply (k : A → ℂ) (f : EuclideanSpace ℂ A) (b : A) :
    operator k f b = ∑ a, k (b + a) * f a := rfl

theorem action_character (k : A → ℂ) (χ : Character A) (b : A) :
    (∑ a, k (b + a) * χ a) = multiplier k χ * χ⁻¹ b := by
  calc
    _ = ∑ c, k c * χ (c - b) := by
      simpa only [Equiv.coe_addLeft, add_sub_cancel_left] using
        Equiv.sum_comp (Equiv.addLeft b) (fun c => k c * χ (c - b))
    _ = multiplier k χ * χ⁻¹ b := by
      simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.inv_apply,
        ← mul_assoc, ← Finset.sum_mul, multiplier]

theorem operator_vector (k : A → ℂ) (χ : Character A) :
    operator k (vector χ) = multiplier k χ • vector χ⁻¹ := by
  ext b
  exact action_character k χ b

theorem operator_normalized (k : A → ℂ) (χ : Character A) :
    operator k (basis χ) = multiplier k χ • basis χ⁻¹ := by
  rw [basis_apply, basis_apply, normalized, normalized, map_smul,
    operator_vector, smul_comm]

theorem multiplier_constant (k : A → ℂ) : multiplier k 0 = ∑ a, k a := by
  simp [multiplier]

theorem orthonormal_sum_norm_sq {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (hv : Orthonormal ℂ v) (c : I → ℂ) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have hi := hv.inner_sum c c Finset.univ
  calc
    _ = RCLike.re (inner ℂ (∑ i, c i • v i) (∑ i, c i • v i)) :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = ∑ i, RCLike.re (inner ℂ (c i) (c i)) := by
      rw [hi, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [RCLike.inner_apply]
      congr 1
      exact mul_comm _ _
    _ = _ := by simp only [← norm_sq_eq_re_inner]

/-- Reusable scalar-to-operator step. The output basis may be permuted. -/
theorem norm_le_of_basis_multipliers {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis I ℂ E) (T : E →ₗ[ℂ] E) (e : I ≃ I)
    (μ : I → ℂ) (i₀ : I) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ i, T (b i) = μ i • b (e i))
    (hμ : ∀ i, i ≠ i₀ → ‖μ i‖ ≤ B)
    (f : E) (hf : inner ℂ (b i₀) f = 0) : ‖T f‖ ≤ B * ‖f‖ := by
  classical
  let c : I → ℂ := fun i => inner ℂ (b i) f
  have he : T f = ∑ i, (c i * μ i) • b (e i) := by
    conv_lhs => rw [← b.sum_repr' f]
    simp only [map_sum, map_smul, hT, smul_smul, c]
  have hnorm : ‖T f‖ ^ 2 = ∑ i, ‖c i * μ i‖ ^ 2 := by
    rw [he]
    exact orthonormal_sum_norm_sq _ (b.orthonormal.comp e e.injective) _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [mul_pow, hnorm]
  calc
    _ ≤ ∑ i, B ^ 2 * ‖c i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = i₀
      · subst i
        simp only [c, hf, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
        exact le_rfl
      · rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hμ i hi)) (sq_nonneg _)
    _ = B ^ 2 * ‖f‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact b.sum_sq_norm_inner_right f

theorem norm_le (k : A → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hμ : ∀ χ : Character A, χ ≠ 0 → ‖multiplier k χ‖ ≤ B)
    (f : EuclideanSpace ℂ A) (hf : ∑ a, f a = 0) :
    ‖operator k f‖ ≤ B * ‖f‖ := by
  exact norm_le_of_basis_multipliers basis (operator k) (Equiv.inv (Character A))
    (multiplier k) 0 B hB (operator_normalized k) hμ f
    (constant_coefficient_eq_zero f hf)

end AES8.PaperCharacterOperator
