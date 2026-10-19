import AESMixing.ByteFourierNorm
import AESMixing.ByteCollision
import AESMixing.TransposeResidual

/-! The complete proved byte-channel interface for the four orientations
needed by the local word argument. The interface packages conclusions. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem aes_squared_walsh_zero_column (v : BinaryWord 8) :
    aesSquaredWalshChannel v 0 = if v = 0 then 1 else 0 := by
  unfold aesSquaredWalshChannel
  rw [field_walsh_zero_first byteCharacter byteCharacter_zero byteCharacter_sum]
  norm_num [BinaryWord.card]
  split_ifs <;> norm_num

theorem aes_squared_walsh_zero_row (u : BinaryWord 8) :
    aesSquaredWalshChannel 0 u = if u = 0 then 1 else 0 := by
  unfold aesSquaredWalshChannel fieldWalsh
  simp only [zero_mul, add_zero]
  simp_rw [mul_comm u]
  rw [real_character_scaled_sum byteCharacter byteCharacter_zero byteCharacter_sum]
  norm_num [BinaryWord.card]
  split_ifs <;> norm_num

theorem aes_squared_walsh_column (u : BinaryWord 8) :
    (∑ v, aesSquaredWalshChannel v u) = 1 := by
  by_cases hu : u = 0
  · subst u; simp only [aes_squared_walsh_zero_column]; simp
  · unfold aesSquaredWalshChannel
    rw [← Finset.sum_div, aes_walsh_second_column u hu]
    norm_num

theorem aes_squared_walsh_row (v : BinaryWord 8) :
    (∑ u, aesSquaredWalshChannel v u) = 1 := by
  by_cases hv : v = 0
  · subst v; simp only [aes_squared_walsh_zero_row]; simp
  · unfold aesSquaredWalshChannel
    rw [← Finset.sum_div, aes_walsh_second_row v hv]
    norm_num

structure ByteResources (D : BinaryWord 8 → BinaryWord 8 → ℝ) : Prop where
  nonnegative : ∀ b a, 0 ≤ D b a
  zero_row : ∀ a, D 0 a = if a = 0 then 1 else 0
  zero_column : ∀ b, D b 0 = if b = 0 then 1 else 0
  column_sum : ∀ a, (∑ b, D b a) = 1
  row_sum : ∀ b, (∑ a, D b a) = 1
  residual : ∀ f : BinaryWord 8 → ℝ, f 0 = 0 → (∑ x, f x) = 0 →
    (∑ y, (∑ x, D y x * f x)^2) ≤ (9 / 128 : ℝ)^2 * ∑ x, f x^2
  collision_column : ∀ a, a ≠ 0 → (∑ b, D b a^2) = 65 / 8192
  collision_row : ∀ b, b ≠ 0 → (∑ a, D b a^2) = 65 / 8192
  atom : ∀ a b, a ≠ 0 → D b a ≤ 1 / 64

theorem ByteResources.transpose {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) : ByteResources (fun b a => D a b) where
  nonnegative b a := h.nonnegative a b
  zero_row := h.zero_column
  zero_column := h.zero_row
  column_sum := h.row_sum
  row_sum := h.column_sum
  residual f hf0 hf := transpose_residual_energy D 0 ((9 / 128 : ℝ)^2)
    h.zero_column h.row_sum h.residual f hf0 hf
  collision_column := h.collision_row
  collision_row := h.collision_column
  atom a b ha := by
    by_cases hb : b = 0
    · subst b
      rw [h.zero_column, if_neg ha]
      norm_num
    · exact h.atom b a hb

theorem aes_byte_resources : ByteResources aesByteChannel where
  nonnegative b a := differenceChannel_nonneg BinaryWord.sboxPerm b a
  zero_row := differenceChannel_zero_row BinaryWord.sboxPerm
  zero_column := differenceChannel_zero_column BinaryWord.sboxPerm
  column_sum := aesByteChannel_column
  row_sum := aesByteChannel_row
  residual := aes_byte_residual
  collision_column := aes_byte_collision_column
  collision_row := aes_byte_collision_row
  atom := aes_byte_atom_bound

theorem aes_fourier_byte_resources : ByteResources aesSquaredWalshChannel where
  nonnegative := aes_squared_walsh_nonnegative
  zero_row := aes_squared_walsh_zero_row
  zero_column := aes_squared_walsh_zero_column
  column_sum := aes_squared_walsh_column
  row_sum := aes_squared_walsh_row
  residual := aes_fourier_byte_residual
  collision_column := aes_squared_walsh_collision_column
  collision_row := aes_squared_walsh_collision_row
  atom := aes_squared_walsh_atom

theorem aes_byte_transpose_resources : ByteResources (fun b a => aesByteChannel a b) :=
  aes_byte_resources.transpose

theorem aes_fourier_byte_transpose_resources :
    ByteResources (fun b a => aesSquaredWalshChannel a b) := aes_fourier_byte_resources.transpose

end AESMixing
