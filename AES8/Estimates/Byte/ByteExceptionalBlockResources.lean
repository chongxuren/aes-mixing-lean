/- Module role: Checked byte-channel resources and certificate consequences.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.FourierLineOverlap
import AESConcrete.ReverseDegreeThree
import AES8.Math.ExceptionalMoments

/-!
# Actual byte residual resources for an exceptional one-sided word block

For any two actual AES byte orientations and every byte
permutation e, H=R1 P_e R2 F is the literal signed byte composition below.
The scaled entries u=8192 H satisfy the entry, energy and zero-sum inputs
required by ExceptionalMoments, in both rows and columns. No word-block
identification or exceptional-support counting is asserted here.
 Constructive
only; no attacks, local execution or manuscript/predecessor edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ByteExceptionalBlockResources
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteGramCore (NonzeroByte)
open AESConcrete.ByteGramDiagonal (actual_gram_diagonal residualGram
  residual_transpose residual_zero_row residual_zero_column residual_row_sum
  residual_column_sum)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.ByteGramFourier (byteFourier_symmetric)
open AESConcrete.FourierLineOverlap (leg_same_flag_gram effectiveOrientation)
open AESConcrete.ReverseDegreeThree (transposeOrientation channel_transpose)

abbrev Byte := BinaryWord 8

-- The local name prevents ambiguity with the topological filter `residual`.
abbrev byteResidual := AESConcrete.ByteLineBounds.residual

def d : ℝ := 8383 / 2088960

theorem residual_transpose_orientation (o : Orientation) (x y : Byte) :
    byteResidual (transposeOrientation o) x y = byteResidual o y x := by
  change residualMatrix (channel (transposeOrientation o)) 0 x y =
    residualMatrix (channel o) 0 y x
  rw [channel_transpose, residual_transpose]

theorem residual_column_energy_le (o : Orientation) (a : Byte) :
    (∑ b, byteResidual o b a ^ 2) ≤ d := by
  have he := actual_gram_diagonal o a
  change (∑ b, byteResidual o b a * byteResidual o b a) = _ at he
  simp only [← pow_two] at he
  rw [he]
  by_cases ha : a = 0 <;> norm_num [ha, d]

theorem residual_row_energy_le (o : Orientation) (b : Byte) :
    (∑ a, byteResidual o b a ^ 2) ≤ d := by
  have he := residual_column_energy_le (transposeOrientation o) b
  simpa only [residual_transpose_orientation] using he

theorem mixed_column_energy_le (o : Orientation) (a : Byte) :
    (∑ b, leg o true b a ^ 2) ≤ d := by
  have he := congrFun (congrFun (leg_same_flag_gram o true) a) a
  change (∑ b, leg o true b a * leg o true b a) =
    residualGram (channel (effectiveOrientation o true)) a a at he
  rw [actual_gram_diagonal] at he
  simp only [← pow_two] at he
  rw [he]
  by_cases ha : a = 0 <;> norm_num [ha, d]

theorem residual_energy_le (o : Orientation) (f : Byte → ℝ) :
    (∑ y, action (byteResidual o) f y ^ 2) ≤ (9 / 128 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  (channel_resources o).residual_matrix_energy f

def H (left right : Orientation) (e : Equiv.Perm Byte) (b a : Byte) : ℝ :=
  ∑ z : Byte, byteResidual left b z * leg right true (e z) a

def u (left right : Orientation) (e : Equiv.Perm Byte) (b a : Byte) : ℝ :=
  8192 * H left right e b a

theorem H_abs_le (left right : Orientation) (e : Equiv.Perm Byte) (b a : Byte) :
    |H left right e b a| ≤ d := by
  have hrow := residual_row_energy_le left b
  have hcol : (∑ z : Byte, leg right true (e z) a ^ 2) ≤ d := by
    rw [Equiv.sum_comp e (fun z => leg right true z a ^ 2)]
    exact mixed_column_energy_le right a
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z => byteResidual left b z) (fun z => leg right true (e z) a)
  have hprod := mul_le_mul hrow hcol
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num [d] : 0 ≤ d)
  apply (sq_le_sq₀ (abs_nonneg _) (by norm_num [d] : 0 ≤ d)).mp
  simp only [sq_abs]
  change (∑ z : Byte, byteResidual left b z * leg right true (e z) a) ^ 2 ≤ d ^ 2
  exact hcs.trans (by nlinarith only [hprod])

theorem u_abs_le (left right : Orientation) (e : Equiv.Perm Byte) (b a : Byte) :
    |u left right e b a| ≤ 33 := by
  unfold u
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8192)]
  exact (mul_le_mul_of_nonneg_left (H_abs_le left right e b a) (by norm_num)).trans
    (by norm_num [d])

theorem H_column_energy_le (left right : Orientation) (e : Equiv.Perm Byte) (a : Byte) :
    (∑ b, H left right e b a ^ 2) ≤ (9 / 128 : ℝ) ^ 2 * d := by
  have he : (fun b => H left right e b a) =
      action (byteResidual left) (fun z => leg right true (e z) a) := rfl
  have hpoint (b : Byte) := congrFun he b
  simp_rw [hpoint]
  apply (residual_energy_le left _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Equiv.sum_comp e (fun z => leg right true z a ^ 2)]
  exact mixed_column_energy_le right a

/-- The row expression is a Fourier transform of the transposed second
residual applied to the first row, with the literal relabeling retained. -/
theorem H_row_fourier (left right : Orientation) (e : Equiv.Perm Byte) (b a : Byte) :
    H left right e b a = byteFourier
      (action (byteResidual (transposeOrientation right))
        (fun z => byteResidual left b (e.symm z))) a := by
  have he := Equiv.sum_comp e (fun z : Byte => byteResidual left b (e.symm z) * leg right true z a)
  simp only [Equiv.symm_apply_apply] at he
  unfold H
  rw [he]
  change (∑ z : Byte, byteResidual left b (e.symm z) *
    ∑ x : Byte, byteResidual right z x * byteFourierMatrix x a) =
      ∑ x : Byte, byteFourierMatrix a x *
        ∑ z : Byte, byteResidual (transposeOrientation right) x z * byteResidual left b (e.symm z)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  rw [residual_transpose_orientation, byteFourier_symmetric x a]
  ring

theorem H_row_energy_le (left right : Orientation) (e : Equiv.Perm Byte) (b : Byte) :
    (∑ a, H left right e b a ^ 2) ≤ (9 / 128 : ℝ) ^ 2 * d := by
  simp_rw [H_row_fourier]
  rw [byteFourier_energy]
  apply (residual_energy_le (transposeOrientation right) _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Equiv.sum_comp e.symm (fun z => byteResidual left b z ^ 2)]
  exact residual_row_energy_le left b

theorem u_column_energy_le (left right : Orientation) (e : Equiv.Perm Byte) (a : Byte) :
    (∑ b, u left right e b a ^ 2) ≤ 1344 := by
  simp only [u, mul_pow, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (H_column_energy_le left right e a)
    (sq_nonneg (8192 : ℝ))).trans (by norm_num [d])

theorem u_row_energy_le (left right : Orientation) (e : Equiv.Perm Byte) (b : Byte) :
    (∑ a, u left right e b a ^ 2) ≤ 1344 := by
  simp only [u, mul_pow, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (H_row_energy_le left right e b)
    (sq_nonneg (8192 : ℝ))).trans (by norm_num [d])

theorem mixed_row_sum (o : Orientation) (b : Byte) : (∑ a, leg o true b a) = 0 := by
  have hrep (a : Byte) : leg o true b a = byteFourier (fun z => byteResidual o b z) a := by
    change (∑ z : Byte, byteResidual o b z * byteFourierMatrix z a) =
      ∑ z : Byte, byteFourierMatrix a z * byteResidual o b z
    apply Finset.sum_congr rfl
    intro z _
    rw [byteFourier_symmetric z a]
    ring
  simp_rw [hrep]
  rw [byteFourier_sum]
  change 16 * residualMatrix (channel o) 0 b 0 = 0
  rw [residual_zero_column (channel_resources o) b, mul_zero]

theorem mixed_column_zero (o : Orientation) (b : Byte) : leg o true b 0 = 0 := by
  change (∑ z : Byte, byteResidual o b z * byteFourierMatrix z 0) = 0
  simp only [byteFourierMatrix, mul_zero, byteCharacter_zero, ← Finset.sum_mul]
  rw [show (∑ z, byteResidual o b z) = 0 from residual_row_sum (channel_resources o) b]
  norm_num

theorem u_row_sum (left right : Orientation) (e : Equiv.Perm Byte) (b : Byte) :
    (∑ a, u left right e b a) = 0 := by
  unfold u H
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, mixed_row_sum, mul_zero, Finset.sum_const_zero]

theorem u_column_sum (left right : Orientation) (e : Equiv.Perm Byte) (a : Byte) :
    (∑ b, u left right e b a) = 0 := by
  unfold u H
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, byteResidual, AESConcrete.ByteLineBounds.residual,
    residual_column_sum (channel_resources left),
    zero_mul, Finset.sum_const_zero, mul_zero]

theorem u_zero_row (left right : Orientation) (e : Equiv.Perm Byte) (a : Byte) :
    u left right e 0 a = 0 := by
  simp only [u, H, byteResidual, AESConcrete.ByteLineBounds.residual, residual_zero_row (channel_resources left),
    zero_mul, Finset.sum_const_zero, mul_zero]

theorem u_zero_column (left right : Orientation) (e : Equiv.Perm Byte) (b : Byte) :
    u left right e b 0 = 0 := by
  simp only [u, H, mixed_column_zero, mul_zero, Finset.sum_const_zero]

theorem nonzero_card : Fintype.card NonzeroByte = 255 := by
  rw [Fintype.card_subtype_compl (fun x : Byte => x = 0), Fintype.card_subtype_eq,
    BinaryWord.card]
  norm_num

theorem sum_nonzero_eq (f : Byte → ℝ) (hf : f 0 = 0) :
    (∑ x : NonzeroByte, f x.val) = ∑ x : Byte, f x := by
  have he := Fintype.sum_eq_add_sum_subtype_ne f 0
  rw [hf, zero_add] at he
  exact he.symm

/-- The scalar exceptional theorem is instantiated by actual byte entries.
The translation parameter is kept explicit until the word-block identity. -/
theorem translated_row_fourth_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (b : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ a : NonzeroByte, ((128 : ℝ) * (u left right e b a.val - c)) ^ 4) <
      25 * 2 ^ 44 := by
  apply AES8.ExceptionalMoments.scaled_translated_fourth_sum_lt
    (fun a : NonzeroByte => u left right e b a.val) c nonzero_card
  · intro a
    exact u_abs_le left right e b a.val
  · rw [sum_nonzero_eq (fun a => u left right e b a ^ 2) (by rw [u_zero_column]; norm_num)]
    exact u_row_energy_le left right e b
  · rw [sum_nonzero_eq _ (u_zero_column left right e b)]
    exact u_row_sum left right e b
  · exact hc0
  · exact hc

theorem translated_column_fourth_lt (left right : Orientation) (e : Equiv.Perm Byte)
    (a : Byte) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ b : NonzeroByte, ((128 : ℝ) * (u left right e b.val a - c)) ^ 4) <
      25 * 2 ^ 44 := by
  apply AES8.ExceptionalMoments.scaled_translated_fourth_sum_lt
    (fun b : NonzeroByte => u left right e b.val a) c nonzero_card
  · intro b
    exact u_abs_le left right e b.val a
  · rw [sum_nonzero_eq (fun b => u left right e b a ^ 2) (by rw [u_zero_row]; norm_num)]
    exact u_column_energy_le left right e a
  · rw [sum_nonzero_eq (fun b => u left right e b a) (u_zero_row left right e a)]
    exact u_column_sum left right e a
  · exact hc0
  · exact hc

end AES8.ByteExceptionalBlockResources
