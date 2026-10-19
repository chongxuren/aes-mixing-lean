import AESMixing.InversionWalsh

/-! Character orthogonality and the differential-linear Fourier identity.
All normalizations are explicit finite sums, using counting measure. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def characterMatrix (ψ : F → ℝ) (y x : F) : ℝ := ψ (y * x)

theorem character_matrix_gram (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hsum : (∑ x, ψ x) = 0) (hchar : ∀ x : F, x + x = 0) (i j : F) :
    gram (characterMatrix ψ) i j = if i = j then (Fintype.card F : ℝ) else 0 := by
  have hz : i + j = 0 ↔ i = j := by
    constructor
    · intro h
      calc
        i = i + (j + j) := by rw [hchar, add_zero]
        _ = j := by rw [← add_assoc, h, zero_add]
    · rintro rfl; exact hchar _
  unfold gram characterMatrix
  simp_rw [← hadd, ← mul_add]
  rw [real_character_scaled_sum ψ hzero hsum]
  simp only [hz]

theorem character_matrix_energy (ψ : F → ℝ) (hzero : ψ 0 = 1)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hsum : (∑ x, ψ x) = 0) (hchar : ∀ x : F, x + x = 0) (f : F → ℝ) :
    (∑ y, (∑ x, ψ (y * x) * f x)^2) =
      Fintype.card F * ∑ x, f x^2 := by
  change (∑ y, (∑ x, characterMatrix ψ y x * f x)^2) = _
  rw [gram_quadratic]
  simp_rw [character_matrix_gram ψ hzero hadd hsum hchar, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq F] in
theorem differential_linear_identity (ψ : F → ℝ)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hchar : ∀ x : F, x + x = 0) (s : Equiv.Perm F) (u v : F) :
    (∑ a, ψ (u * a) * (∑ x, ψ (v * difference s a x))) = fieldWalsh ψ s u v ^ 2 := by
  let t : F → ℝ := fun x => ψ (u * x + v * s x)
  have hneg (x : F) : -x = x := by
    exact add_right_cancel ((neg_add_cancel x).trans (hchar x).symm)
  have hp (a x : F) : ψ (u * a) * ψ (v * difference s a x) = t (x + a) * t x := by
    dsimp only [t]
    rw [← hadd, ← hadd]
    congr 1
    simp only [difference, sub_eq_add_neg, hneg]
    have he : (u * (x + a) + v * s (x + a)) + (u * x + v * s x) =
        (u * x + u * x) + (u * a + v * (s (x + a) + s x)) := by ring
    rw [he, hchar, zero_add]
  simp_rw [Finset.mul_sum, hp]
  rw [Finset.sum_comm]
  have hs (x : F) : (∑ a, t (x + a) * t x) = (∑ y, t y) * t x := by
    rw [← Finset.sum_mul]
    congr 1
    exact Equiv.sum_comp (Equiv.addLeft x) t
  simp_rw [hs]
  rw [← Finset.mul_sum]
  change fieldWalsh ψ s u v * fieldWalsh ψ s u v = fieldWalsh ψ s u v ^ 2
  ring

theorem fourier_ddt_identity (ψ : F → ℝ)
    (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hchar : ∀ x : F, x + x = 0) (s : Equiv.Perm F) (u v : F) :
    (∑ a, ψ (u * a) * (∑ b, ψ (v * b) * differenceChannel s b a)) =
      fieldWalsh ψ s u v ^ 2 / Fintype.card F := by
  simp_rw [← difference_channel_average s _ (fun b => ψ (v * b)), ← mul_div_assoc]
  rw [← Finset.sum_div, differential_linear_identity ψ hadd hchar]

end AESMixing
