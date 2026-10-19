import AESConcrete.ByteColumnMoments
import AESConcrete.SingleByteCoordinates
import AESConcrete.WordColumnBounds

/-!
# Actual single-active-byte AES word-column bound

For a nonzero word with only one active input byte, the four output labels
are zero-fixing permutations of the same source. Their Gram factors
need not coincide. The weighted fourth-moment comparison retains this common
source, then exact word centering subtracts 1/(2^32-1).

This proves only the one-active-byte case of the residual column target.
Columns with two or more active input bytes require the restricted-MDS
marginal argument, which is not asserted here. Constructive mathematics only;
no attacks, manuscript edits, or whole-experiment identification.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SingleByteColumnBound
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteGramCore (NonzeroByte)
open AESConcrete.WordColumnGram (Byte Word singleByteWord)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)
open AESConcrete.ColumnFourthMoment
open AESConcrete.ByteColumnMoments
open AESConcrete.SingleByteCoordinates

/-- Full column energy bounded using the actual four correlated coordinates. -/
theorem full_column_energy_le (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) ≤ aesFourthBound := by
  let G : Fin 4 → NonzeroByte → NonzeroByte → ℝ := fun i x z =>
    gram (channel left) (coordinatePerm inverse k i x.val) (coordinatePerm inverse k i z.val)
  have hg (i : Fin 4) : weightedMoment (nonzeroColumn right (a k)) (G i) 4 ≤
      aesFourthBound :=
    permuted_column_fourth_moment left right (coordinatePerm inverse k i)
      (coordinatePerm_zero inverse k i) (a k) ha
  have hb := weighted_four_product_le (nonzeroColumn right (a k))
    (G 0) (G 1) (G 2) (G 3) aesFourthBound
    (fun x => (channel_resources right).nonnegative _ _) (hg 0) (hg 1) (hg 2) (hg 3)
  rw [WordColumnGram.actual_single_active_nonzero_column_gram left right inverse a k hsupport ha]
  simpa [G, nonzeroColumn, coordinatePerm_apply,
    Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, mul_assoc] using hb

theorem full_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) <
      (17 / (15 * 4294967296) : ℝ) :=
  (full_column_energy_le left right inverse a k hsupport ha).trans_lt aesFourthBound_lt

/-- The desired residual column cap is discharged for every single-byte input,
for all four explicit byte-channel orientations and both diffusion directions. -/
theorem residual_column_energy_lt (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) := by
  have hane : a ≠ 0 := by
    intro hz
    exact ha (congrFun hz k)
  rw [pointed_residual_column_energy_exact (word_kernel_pointed left right inverse)
    AES.word_card_gt_one a hane, AES.word_card_exact]
  have h := full_column_energy_lt left right inverse a k hsupport ha
  norm_num at h ⊢
  linarith

theorem residual_zero_column_energy (left right : Orientation) (inverse : Bool) :
    (∑ y : Word, residualMatrix (wordKernel left right inverse) 0 y 0 ^ 2) = 0 := by
  simp only [pointed_residual_zero_column (word_kernel_pointed left right inverse),
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

theorem actual_word_single_byte_residual (a : Word) (k : Fin 4)
    (hsupport : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    (∑ y : Word, residualMatrix AES.wordSuperboxKernel 0 y a ^ 2) <
      (2 / (15 * 4294967296) : ℝ) :=
  residual_column_energy_lt .ordinary .ordinary false a k hsupport ha

end AESConcrete.SingleByteColumnBound
