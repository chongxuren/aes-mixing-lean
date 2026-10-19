import AESMixing.AESWalshBounds

/-! Normalized Fourier conjugation of the concrete byte DDT. Its residual
bound follows from the proved AES norm and Fourier isometry. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def matrixProduct {α β γ : Type*} [Fintype β]
    (A : γ → β → ℝ) (B : β → α → ℝ) (y : γ) (x : α) : ℝ :=
  ∑ z, A y z * B z x

theorem action_matrixProduct {α β γ : Type*} [Fintype α] [Fintype β]
    (A : γ → β → ℝ) (B : β → α → ℝ) (f : α → ℝ) :
    action (matrixProduct A B) f = action A (action B f) := by
  funext y
  simp only [action, matrixProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

def byteFourierMatrix (y x : BinaryWord 8) : ℝ := byteCharacter (y * x) / 16
def byteFourier (f : BinaryWord 8 → ℝ) : BinaryWord 8 → ℝ := action byteFourierMatrix f

theorem byteFourier_apply (f : BinaryWord 8 → ℝ) (y : BinaryWord 8) :
    byteFourier f y = (∑ x, byteCharacter (y * x) * f x) / 16 := by
  simp only [byteFourier, action, byteFourierMatrix, div_mul_eq_mul_div, Finset.sum_div]

theorem byteFourier_energy (f : BinaryWord 8 → ℝ) :
    (∑ y, byteFourier f y ^ 2) = ∑ x, f x^2 := by
  simp_rw [byteFourier_apply, div_pow]
  rw [← Finset.sum_div, character_matrix_energy byteCharacter byteCharacter_zero
    byteCharacter_add byteCharacter_sum BinaryWord.add_self]
  norm_num [BinaryWord.card]

theorem byteFourier_at_zero (f : BinaryWord 8 → ℝ) :
    byteFourier f 0 = (∑ x, f x) / 16 := by
  simp only [byteFourier_apply, zero_mul, byteCharacter_zero, one_mul]

theorem byteFourier_sum (f : BinaryWord 8 → ℝ) : (∑ y, byteFourier f y) = 16 * f 0 := by
  simp_rw [byteFourier_apply]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hs (x : BinaryWord 8) : (∑ y, byteCharacter (y * x)) =
      if x = 0 then 256 else 0 := by
    have h := real_character_scaled_sum byteCharacter byteCharacter_zero byteCharacter_sum x
    norm_num only [BinaryWord.card] at h
    exact h
  simp_rw [hs, ite_mul, zero_mul]
  simp
  ring

theorem byteFourier_ddt_coefficient (v u : BinaryWord 8) :
    matrixProduct byteFourierMatrix (matrixProduct aesByteChannel byteFourierMatrix) v u =
      aesSquaredWalshChannel v u := by
  have he : matrixProduct byteFourierMatrix (matrixProduct aesByteChannel byteFourierMatrix) v u =
      (∑ a, byteCharacter (u * a) *
        (∑ b, byteCharacter (v * b) * aesByteChannel b a)) / 256 := by
    unfold matrixProduct byteFourierMatrix
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm u a]
    ring
  rw [he]
  unfold aesByteChannel
  rw [fourier_ddt_identity byteCharacter byteCharacter_add BinaryWord.add_self]
  unfold aesSquaredWalshChannel
  norm_num [BinaryWord.card]
  ring

theorem byteFourier_ddt_action (f : BinaryWord 8 → ℝ) :
    byteFourier (action aesByteChannel (byteFourier f)) = action aesSquaredWalshChannel f := by
  unfold byteFourier
  rw [← action_matrixProduct aesByteChannel byteFourierMatrix f,
    ← action_matrixProduct byteFourierMatrix (matrixProduct aesByteChannel byteFourierMatrix) f]
  congr 1
  funext v u
  exact byteFourier_ddt_coefficient v u

theorem aes_fourier_byte_residual (f : BinaryWord 8 → ℝ)
    (hf0 : f 0 = 0) (hf : ∑ x, f x = 0) :
    (∑ y, action aesSquaredWalshChannel f y ^ 2) ≤
      (9 / 128 : ℝ)^2 * ∑ x, f x^2 := by
  rw [← byteFourier_ddt_action, byteFourier_energy]
  have h := aes_byte_residual (byteFourier f)
    (by rw [byteFourier_at_zero, hf, zero_div])
    (by rw [byteFourier_sum, hf0, mul_zero])
  rw [byteFourier_energy] at h
  exact h

end AESMixing
