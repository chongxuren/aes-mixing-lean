import AES8.Math.PaperActivityInputAssembly

/-! From exact support and squared response energies to signed block energy.
The support row-Gram is explicit. This leaf has no physical AES interface. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputSupportAssembly
open AESMixing PaperActivityInputAssembly
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X] [DecidableEq B]

/-- Uniform squared entry caps multiply the exact Boolean support row-Gram. -/
theorem support_energy (P : A → B → Prop) [∀ a b, Decidable (P a b)]
    (cap : ℝ) (hcap : 0 ≤ cap) (g : ℝ) (hg : 0 ≤ g)
    (hgram : ∀ a, (∑ a', ∑ b,
      (if P a b then (1 : ℝ) else 0) * (if P a' b then (1 : ℝ) else 0)) ≤ g)
    (w : A → B → X → ℝ)
    (hw : ∀ a b, (∑ x, w a b x ^ 2) ≤ if P a b then cap else 0)
    (c : B → ℝ) :
    (∑ a, ∑ x, (∑ b, c b * w a b x)^2) ≤ g*cap*∑ b, c b^2 := by
  let C : A → B → ℝ := fun a b => Real.sqrt cap * (if P a b then 1 else 0)
  have hC : ∀ a b, 0 ≤ C a b := by intro a b; dsimp [C]; positivity
  have hlen (a : A) (b : B) : l2 (w a b) ≤ C a b := by
    have h := hw a b
    by_cases hp : P a b
    · simp only [if_pos hp] at h
      dsimp [C]
      rw [if_pos hp,mul_one]
      apply (sq_le_sq₀ (l2_nonneg _) (Real.sqrt_nonneg _)).mp
      simpa only [l2_sq,Real.sq_sqrt hcap] using h
    · simp only [if_neg hp] at h
      dsimp [C]
      rw [if_neg hp,mul_zero]
      have hs := l2_sq (w a b)
      nlinarith [l2_nonneg (w a b)]
  have hscale (a a' : A) (b : B) :
      C a b * C a' b = cap *
        ((if P a b then (1 : ℝ) else 0) * (if P a' b then (1 : ℝ) else 0)) := by
    dsimp [C]
    by_cases hp : P a b <;> by_cases hq : P a' b <;>
      simp [hp,hq,← pow_two,Real.sq_sqrt hcap]
  apply vector_block_energy w C hC hlen (g*cap) (mul_nonneg hg hcap)
  · intro a a'
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (hC a b) (hC a' b))
  · intro a
    simp_rw [hscale]
    simp_rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (hgram a) hcap
    simpa only [mul_comm] using h

/-- A single output frame row sums the individual squared entry caps. -/
theorem single_row_energy (hA : Fintype.card A = 1)
    (cap : B → ℝ) (hcap : ∀ b, 0 ≤ cap b)
    (w : A → B → X → ℝ)
    (hw : ∀ a b, (∑ x, w a b x ^ 2) ≤ cap b) (c : B → ℝ) :
    (∑ a, ∑ x, (∑ b, c b * w a b x)^2) ≤
      (∑ b, cap b)*∑ b, c b^2 := by
  let C : A → B → ℝ := fun _ b => Real.sqrt (cap b)
  have hC : ∀ a b, 0 ≤ C a b := by intro a b; exact Real.sqrt_nonneg _
  have hlen (a : A) (b : B) : l2 (w a b) ≤ C a b := by
    apply (sq_le_sq₀ (l2_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [l2_sq,Real.sq_sqrt (hcap b)] using hw a b
  apply vector_block_energy w C hC hlen (∑ b, cap b)
    (Finset.sum_nonneg (fun b _ => hcap b))
  · intro a a'
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (hC a b) (hC a' b))
  · intro a
    simp only [C,← pow_two,Real.sq_sqrt (hcap _),Finset.sum_const,
      Finset.card_univ,hA,nsmul_eq_mul, Nat.cast_one,one_mul,le_refl]

end AES8.PaperActivityInputSupportAssembly
