import AESConcrete.ByteGramDiagonal

/-!
# Actual inversion byte Gram and AES affine relabeling

This module supplies the algebraic meaning of the finite one-variable byte
Gram profile. The inversion Gram is obtained from the actual difference
channel. Its formula uses the already proved inversion sign Gram; it is
not an assumed overlap table. AES affine output relabeling and transpose
are kept explicit. Fourier transport and finite moment resources belong
to separate modules. Constructive scope only; no attack work.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteGramCore
open AESMixing
open AESConcrete.ByteGramDiagonal (residualGram)

abbrev Byte := BinaryWord 8
abbrev NonzeroByte := {x : Byte // x ≠ 0}

def inversionChannel : Byte → Byte → ℝ := differenceChannel invPermutation

def inversionGram : Byte → Byte → ℝ := residualGram inversionChannel

theorem activity_relabel_left (e : Equiv.Perm Byte) (he : e 0 = 0)
    (a b : Byte) : activityMatrix 0 (e a) b = activityMatrix 0 a b := by
  have hz : e a = 0 ↔ a = 0 := by
    constructor
    · intro h
      exact e.injective (h.trans he.symm)
    · rintro rfl
      exact he
  simp only [activityMatrix, hz]

theorem activity_relabel_right (e : Equiv.Perm Byte) (he : e 0 = 0)
    (a b : Byte) : activityMatrix 0 a (e b) = activityMatrix 0 a b := by
  rw [ByteGramDiagonal.activity_symmetric, activity_relabel_left e he,
    ByteGramDiagonal.activity_symmetric]

theorem inversion_residual_symmetric (a b : Byte) :
    residualMatrix inversionChannel 0 a b = residualMatrix inversionChannel 0 b a := by
  unfold residualMatrix inversionChannel
  rw [inversion_channel_symmetric, ByteGramDiagonal.activity_symmetric]

theorem aes_residual_affine (a b : Byte) :
    residualMatrix aesByteChannel 0 a b =
      residualMatrix inversionChannel 0 (AES.affineLinearEquiv.symm a) b := by
  unfold residualMatrix inversionChannel
  rw [aesByteChannel_affine]
  have h := activity_relabel_left AES.affineLinearEquiv.symm.toEquiv
    (map_zero AES.affineLinearEquiv.symm) a b
  exact congrArg (fun t => differenceChannel invPermutation
    (AES.affineLinearEquiv.symm a) b - t) h.symm

theorem gram_relabel_output (D : Byte → Byte → ℝ) (e : Equiv.Perm Byte)
    (a b : Byte) : gram (fun y x => D (e y) x) a b = gram D a b :=
  Equiv.sum_comp e (fun y => D y a * D y b)

theorem aes_gram (a b : Byte) : residualGram aesByteChannel a b = inversionGram a b := by
  change (∑ y, residualMatrix aesByteChannel 0 y a * residualMatrix aesByteChannel 0 y b) =
    ∑ y, residualMatrix inversionChannel 0 y a * residualMatrix inversionChannel 0 y b
  simp_rw [aes_residual_affine]
  exact Equiv.sum_comp AES.affineLinearEquiv.symm.toEquiv
    (fun y => residualMatrix inversionChannel 0 y a * residualMatrix inversionChannel 0 y b)

theorem aes_transpose_gram (a b : Byte) :
    residualGram (fun y x => aesByteChannel x y) a b =
      inversionGram (AES.affineLinearEquiv.symm a) (AES.affineLinearEquiv.symm b) := by
  have hres (y x : Byte) : residualMatrix (fun y x => aesByteChannel x y) 0 y x =
      residualMatrix inversionChannel 0 y (AES.affineLinearEquiv.symm x) := by
    rw [ByteGramDiagonal.residual_transpose, aes_residual_affine,
      inversion_residual_symmetric (AES.affineLinearEquiv.symm x) y]
  change (∑ y, residualMatrix (fun y x => aesByteChannel x y) 0 y a *
      residualMatrix (fun y x => aesByteChannel x y) 0 y b) = _
  simp_rw [hres]
  rfl

theorem inversion_gram_formula (a b : Byte) :
    inversionGram a b = gram inversionChannel a b - activityMatrix 0 a b := by
  rw [← aes_gram, ByteGramDiagonal.residual_gram_formula aes_byte_resources]
  congr 1
  unfold gram
  simp_rw [aesByteChannel_affine]
  exact Equiv.sum_comp AES.affineLinearEquiv.symm.toEquiv
    (fun y => inversionChannel y a * inversionChannel y b)

theorem inversion_gram_symmetric (a b : Byte) : inversionGram a b = inversionGram b a := by
  unfold inversionGram residualGram gram
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem inversion_gram_zero_row (a : Byte) : inversionGram 0 a = 0 := by
  rw [← aes_gram]
  exact ByteGramDiagonal.residual_gram_zero_row aes_byte_resources a

theorem inversion_gram_zero_column (a : Byte) : inversionGram a 0 = 0 := by
  rw [← aes_gram]
  exact ByteGramDiagonal.residual_gram_zero_column aes_byte_resources a

theorem inversion_gram_row_sum (a : Byte) : (∑ b, inversionGram a b) = 0 := by
  simp_rw [← aes_gram]
  exact ByteGramDiagonal.residual_gram_row_sum aes_byte_resources a

theorem inversion_gram_column_sum (a : Byte) : (∑ b, inversionGram b a) = 0 := by
  simp_rw [← aes_gram]
  exact ByteGramDiagonal.residual_gram_column_sum aes_byte_resources a

private def sign (y a : NonzeroByte) : ℝ := inversionSignMatrix byteCharacter y a

private def inverseDelta (y a : NonzeroByte) : ℝ :=
  if nonzeroInvPermutation y = a then 1 else 0

private theorem nonzero_ones_sum : (∑ _ : NonzeroByte, (1 : ℝ)) = 255 := by
  norm_num [NonzeroByte, BinaryWord.card]

private theorem sign_sum (a : NonzeroByte) : (∑ y, sign y a) = -1 := by
  calc
    _ = ∑ y : NonzeroByte, byteCharacter (y.val * a.val⁻¹) :=
      Equiv.sum_comp (nonzeroInvPermutation (F := Byte))
        (fun y : NonzeroByte => byteCharacter (y.val * a.val⁻¹))
    _ = -1 := by
      rw [real_character_nonzero_sum byteCharacter byteCharacter_zero byteCharacter_sum]
      simp [a.property]

private theorem inverseDelta_sum (a : NonzeroByte) : (∑ y, inverseDelta y a) = 1 := by
  have h := Equiv.sum_comp (nonzeroInvPermutation (F := Byte))
    (fun y : NonzeroByte => if y = a then (1 : ℝ) else 0)
  simpa only [inverseDelta, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

private theorem sign_inverseDelta_sum (a b : NonzeroByte) :
    (∑ y, sign y a * inverseDelta y b) = byteCharacter (b.val / a.val) := by
  calc
    _ = ∑ y : NonzeroByte,
        sign (nonzeroInvPermutation.symm y) a * (if y = b then 1 else 0) := by
      simpa only [inverseDelta, Equiv.apply_symm_apply] using
        (Equiv.sum_comp (nonzeroInvPermutation (F := Byte)).symm
          (fun y => sign y a * inverseDelta y b)).symm
    _ = sign (nonzeroInvPermutation.symm b) a := by simp
    _ = byteCharacter (b.val / a.val) := by
      change byteCharacter ((b.val⁻¹)⁻¹ * a.val⁻¹) = _
      simp only [inv_inv, div_eq_mul_inv]

private theorem inverseDelta_product_sum (a b : NonzeroByte) :
    (∑ y, inverseDelta y a * inverseDelta y b) = if a = b then 1 else 0 := by
  calc
    _ = ∑ y : NonzeroByte,
        (if y = a then (1 : ℝ) else 0) * (if y = b then 1 else 0) := by
      simpa only [inverseDelta, Equiv.apply_symm_apply] using
        (Equiv.sum_comp (nonzeroInvPermutation (F := Byte)).symm
          (fun y => inverseDelta y a * inverseDelta y b)).symm
    _ = _ := by
      by_cases hab : a = b <;> simp [hab, eq_comm]

/-- The exact ordinary inversion-channel overlap. The sign Gram handles
the only character-product sum; the other terms are permutation deltas. -/
theorem inversion_raw_gram_nonzero (a b : NonzeroByte) :
    gram inversionChannel a.val b.val =
      (256 + 260 * (if a = b then 1 else 0) +
        2 * byteCharacter (b.val / a.val) + 2 * byteCharacter (a.val / b.val)) / 65536 := by
  have hsign : (∑ y, sign y a * sign y b) =
      (if a = b then (256 : ℝ) else 0) - 1 := byte_inversion_sign_gram a b
  have hex (y : NonzeroByte) :
      (1 + sign y a + 2 * inverseDelta y a) *
        (1 + sign y b + 2 * inverseDelta y b) =
      1 + sign y a + sign y b + sign y a * sign y b +
        2 * inverseDelta y a + 2 * inverseDelta y b +
        2 * (sign y a * inverseDelta y b) +
        2 * (sign y b * inverseDelta y a) +
        4 * (inverseDelta y a * inverseDelta y b) := by ring
  have htotal : (∑ y : NonzeroByte,
      (1 + sign y a + 2 * inverseDelta y a) *
        (1 + sign y b + 2 * inverseDelta y b)) =
      256 + 260 * (if a = b then 1 else 0) +
        2 * byteCharacter (b.val / a.val) + 2 * byteCharacter (a.val / b.val) := by
    simp_rw [hex]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [nonzero_ones_sum, sign_sum, sign_sum, hsign,
      inverseDelta_sum, inverseDelta_sum,
      sign_inverseDelta_sum, sign_inverseDelta_sum, inverseDelta_product_sum]
    split_ifs <;> ring
  unfold gram inversionChannel
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun y => differenceChannel invPermutation y a.val * differenceChannel invPermutation y b.val) 0]
  simp only [differenceChannel_zero_row, if_neg a.property, if_neg b.property,
    zero_mul, zero_add]
  change (∑ y : NonzeroByte,
    differenceChannel invPermutation y.val a.val * differenceChannel invPermutation y.val b.val) = _
  simp_rw [byte_inversion_formula a, byte_inversion_formula b]
  change (∑ y : NonzeroByte,
    ((1 + sign y a + 2 * inverseDelta y a) / 256) *
      ((1 + sign y b + 2 * inverseDelta y b) / 256)) = _
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div, htotal]
  norm_num

/-- Common signed Gram formula on nonzero labels. The activity correction
is subtracted after forming the actual channel Gram. -/
theorem inversion_gram_nonzero (a b : Byte) (ha : a ≠ 0) (hb : b ≠ 0) :
    inversionGram a b =
      (65 / 16384 : ℝ) * (if a = b then 1 else 0) +
        (1 / 32768 : ℝ) * (byteCharacter (a / b) + byteCharacter (b / a)) -
        1 / 65280 := by
  rw [inversion_gram_formula, inversion_raw_gram_nonzero ⟨a, ha⟩ ⟨b, hb⟩]
  have he : (⟨a, ha⟩ : NonzeroByte) = ⟨b, hb⟩ ↔ a = b := Subtype.ext_iff
  simp only [he, activityMatrix, if_neg ha, if_neg hb, BinaryWord.card]
  norm_num
  split_ifs <;> ring

end AESConcrete.ByteGramCore
