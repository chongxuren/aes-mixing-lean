import AES8.Math.ExceptionalConvexEnvelope
import AES8.Estimates.Byte.ByteExceptionalBlockResources

/-! Literal current-paper convex-envelope bounds on actual exceptional byte
blocks. The scaled endpoints pass through the printed 1623000 intermediate
before supplying the word-block consumer. Historical sufficient bounds remain
in ByteExceptionalBlockResources and are not quantitative premises here. -/
noncomputable section
open scoped BigOperators
namespace AES8.ByteExceptionalEnvelope
open AESMixing ByteExceptionalBlockResources
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteGramCore (NonzeroByte)
set_option autoImplicit false

/-- The current printed cubic allowance for each physical byte row. -/
theorem row_cubic_le (left right : Orientation) (e : Equiv.Perm Byte) (b : Byte) :
    (∑ a : NonzeroByte, |u left right e b a.val| ^ 3) ≤ 40033 := by
  apply ExceptionalConvexEnvelope.cubic_sum_le_40033
  · intro a; exact u_abs_le left right e b a.val
  · rw [sum_nonzero_eq (fun a => u left right e b a ^ 2) (by rw [u_zero_column]; norm_num)]
    exact u_row_energy_le left right e b

/-- The current printed cubic allowance for each physical byte column. -/
theorem column_cubic_le (left right : Orientation) (e : Equiv.Perm Byte) (a : Byte) :
    (∑ b : NonzeroByte, |u left right e b.val a| ^ 3) ≤ 40033 := by
  apply ExceptionalConvexEnvelope.cubic_sum_le_40033
  · intro b; exact u_abs_le left right e b.val a
  · rw [sum_nonzero_eq (fun b => u left right e b a ^ 2) (by rw [u_zero_row]; norm_num)]
    exact u_column_energy_le left right e a

theorem translated_row_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (b : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ a : NonzeroByte, (u left right e b a.val - c) ^ 4) < 1623000 := by
  apply ExceptionalConvexEnvelope.translated_fourth_sum_lt_1623000
    (fun a : NonzeroByte => u left right e b a.val) c nonzero_card
  · intro a; exact u_abs_le left right e b a.val
  · rw [sum_nonzero_eq (fun a => u left right e b a ^ 2) (by rw [u_zero_column]; norm_num)]
    exact u_row_energy_le left right e b
  · rw [sum_nonzero_eq (fun a => u left right e b a) (u_zero_column left right e b)]
    exact u_row_sum left right e b
  · exact hc0
  · exact hc

theorem translated_column_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (a : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ b : NonzeroByte, (u left right e b.val a - c) ^ 4) < 1623000 := by
  apply ExceptionalConvexEnvelope.translated_fourth_sum_lt_1623000
    (fun b : NonzeroByte => u left right e b.val a) c nonzero_card
  · intro b; exact u_abs_le left right e b.val a
  · rw [sum_nonzero_eq (fun b => u left right e b a ^ 2) (by rw [u_zero_row]; norm_num)]
    exact u_column_energy_le left right e a
  · rw [sum_nonzero_eq (fun b => u left right e b a) (u_zero_row left right e a)]
    exact u_column_sum left right e a
  · exact hc0
  · exact hc

/-- Scale the printed convex-envelope row estimate to the word-block allowance.
The intermediate 1623000 is retained in this dependency path. -/
theorem scaled_row_fourth_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (b : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ a : NonzeroByte, ((128 : ℝ) * (u left right e b a.val - c)) ^ 4) <
      25 * 2 ^ 44 := by
  have h := translated_row_lt left right e b c hc0 hc
  calc
    _ = (128 : ℝ) ^ 4 * ∑ a : NonzeroByte, (u left right e b a.val - c) ^ 4 := by
      simp only [mul_pow, Finset.mul_sum]
    _ < (128 : ℝ) ^ 4 * 1623000 := mul_lt_mul_of_pos_left h (by norm_num)
    _ < 25 * 2 ^ 44 := by norm_num

/-- The same printed scaling for columns of the actual byte block. -/
theorem scaled_column_fourth_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (a : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ b : NonzeroByte, ((128 : ℝ) * (u left right e b.val a - c)) ^ 4) <
      25 * 2 ^ 44 := by
  have h := translated_column_lt left right e a c hc0 hc
  calc
    _ = (128 : ℝ) ^ 4 * ∑ b : NonzeroByte, (u left right e b.val a - c) ^ 4 := by
      simp only [mul_pow, Finset.mul_sum]
    _ < (128 : ℝ) ^ 4 * 1623000 := mul_lt_mul_of_pos_left h (by norm_num)
    _ < 25 * 2 ^ 44 := by norm_num

end AES8.ByteExceptionalEnvelope
