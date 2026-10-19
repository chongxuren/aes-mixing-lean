import AESConcrete.ByteGramResources

/-!
# One-sided Fourier bound for actual byte residual Grams

The inversion Gram's mixed row is evaluated by the signed Gram formula,
character orthogonality, and the already checked inversion Walsh bound.
The extremal mask is handled with the checked Walsh value at one. Actual
AES orientations use independent row/column relabelings from ByteGramFourier.
No word bound or new byte estimate is assumed. Constructive scope only.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteGramMixed
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramResources
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)

private theorem character_nonzero_sum (k : Byte) (hk : k ≠ 0) :
    (∑ c : NonzeroByte, byteCharacter (k * c.val)) = -1 := by
  simp_rw [mul_comm k]
  rw [real_character_nonzero_sum byteCharacter byteCharacter_zero byteCharacter_sum]
  simp [hk]

private theorem character_product_sum (k : Byte) :
    (∑ c : NonzeroByte, byteCharacter c.val * byteCharacter (k * c.val)) =
      (if k = 1 then (256 : ℝ) else 0) - 1 := by
  have heq : k + 1 = 0 ↔ k = 1 := by
    constructor
    · intro h
      calc
        k = k + (1 + 1) := by rw [BinaryWord.add_self, add_zero]
        _ = 1 := by rw [← add_assoc, h, zero_add]
    · rintro rfl
      exact BinaryWord.add_self 1
  have hterm (c : NonzeroByte) : byteCharacter c.val * byteCharacter (k * c.val) =
      byteCharacter (c.val * (k + 1)) := by
    rw [← byteCharacter_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [real_character_nonzero_sum byteCharacter byteCharacter_zero byteCharacter_sum]
  simp only [heq, BinaryWord.card]
  norm_num

private theorem character_inverse_product_sum (k : Byte) :
    (∑ c : NonzeroByte, byteCharacter c.val⁻¹ * byteCharacter (k * c.val)) =
      fieldWalsh byteCharacter (fun x => x⁻¹) 1 k - 1 := by
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun c : Byte => byteCharacter (k * c + 1 * c⁻¹)) 0
  have hterm (c : NonzeroByte) :
      byteCharacter c.val⁻¹ * byteCharacter (k * c.val) =
        byteCharacter (k * c.val + 1 * c.val⁻¹) := by
    rw [← byteCharacter_add, one_mul, add_comm]
  simp_rw [hterm]
  change fieldWalsh byteCharacter (fun x => x⁻¹) k 1 = _ at hsplit
  simp only [mul_zero, inv_zero, one_mul, add_zero, byteCharacter_zero] at hsplit
  rw [inversion_walsh_symmetric byteCharacter k 1] at hsplit
  simp only [one_mul]
  linarith

private theorem delta_character_sum (k : Byte) :
    (∑ c : NonzeroByte, (if c.val = 1 then (1 : ℝ) else 0) *
      byteCharacter (k * c.val)) = byteCharacter k := by
  classical
  let oneByte : NonzeroByte := ⟨1, by decide⟩
  rw [Finset.sum_eq_single oneByte]
  · simp [oneByte]
  · intro c _ hc
    have hc1 : c.val ≠ 1 := by
      intro h
      exact hc (Subtype.ext h)
    simp [hc1]
  · intro h
    exact (h (Finset.mem_univ oneByte)).elim

/-- The mixed coefficient is a scalar Walsh expression. This is the
actual residual Gram multiplied by the normalized byte Fourier matrix. -/
theorem inversion_mixed_row_formula (k : Byte) (hk : k ≠ 0) :
    kernelCompose inversionGram byteFourierMatrix 1 k =
      (-191 + 32640 * (if k = 1 then 1 else 0) +
        (255 / 2 : ℝ) * fieldWalsh byteCharacter (fun x => x⁻¹) 1 k +
        16575 * byteCharacter k) / (16 * 4177920) := by
  have hg (c : NonzeroByte) : inversionGram 1 c.val =
      (65 / 16384 : ℝ) * (if c.val = 1 then 1 else 0) +
        (1 / 32768 : ℝ) * (byteCharacter c.val⁻¹ + byteCharacter c.val) - 1 / 65280 := by
    rw [inversion_gram_nonzero 1 c.val (by decide) c.property]
    simp only [one_div, div_one, eq_comm]
  have hterm (c : NonzeroByte) : inversionGram 1 c.val * byteFourierMatrix c.val k =
      ((65 / 16384 : ℝ) * ((if c.val = 1 then 1 else 0) * byteCharacter (k * c.val)) +
        (1 / 32768 : ℝ) * (byteCharacter c.val⁻¹ * byteCharacter (k * c.val)) +
        (1 / 32768 : ℝ) * (byteCharacter c.val * byteCharacter (k * c.val)) -
        (1 / 65280 : ℝ) * byteCharacter (k * c.val)) / 16 := by
    rw [hg]
    unfold byteFourierMatrix
    rw [mul_comm c.val k]
    ring
  unfold kernelCompose
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun c => inversionGram 1 c * byteFourierMatrix c k) 0]
  simp only [inversion_gram_zero_column, zero_mul, zero_add]
  simp_rw [hterm]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [delta_character_sum, character_inverse_product_sum, character_product_sum,
    character_nonzero_sum k hk]
  split_ifs <;> ring

theorem inversion_mixed_zero (a : Byte) :
    kernelCompose inversionGram byteFourierMatrix a 0 = 0 := by
  unfold kernelCompose byteFourierMatrix
  simp only [mul_zero, byteCharacter_zero]
  rw [← Finset.sum_mul, inversion_gram_row_sum, zero_mul]

private theorem inversion_walsh_one :
    fieldWalsh byteCharacter (fun x : Byte => x⁻¹) 1 1 = 32 := by
  rw [byte_walsh_one_lookup, AES.inversionWalshLookup_correct]
  exact_mod_cast ByteGramFinite.kloosterman_one

private theorem character_one : byteCharacter (1 : Byte) = 1 := by
  have h : AES.traceBit (1 : BitVec 8) = false := by decide
  change (if AES.traceBit (1 : BitVec 8) then (-1 : ℝ) else 1) = 1
  rw [h]
  rfl

theorem inversion_mixed_at_one :
    kernelCompose inversionGram byteFourierMatrix 1 1 = (13276 / (4 * 4177920) : ℝ) := by
  rw [inversion_mixed_row_formula 1 (by decide), if_pos rfl,
    inversion_walsh_one, character_one]
  norm_num

theorem inversion_mixed_row_bound (k : Byte) :
    |kernelCompose inversionGram byteFourierMatrix 1 k| ≤ (13276 / (4 * 4177920) : ℝ) := by
  by_cases hk : k = 0
  · subst k
    rw [inversion_mixed_zero]
    norm_num
  by_cases hk1 : k = 1
  · subst k
    rw [inversion_mixed_at_one]
    norm_num
  have hw := byte_walsh_one_bound k
  have hwlo : -32 ≤ fieldWalsh byteCharacter (fun x => x⁻¹) 1 k := by
    nlinarith [sq_nonneg (fieldWalsh byteCharacter (fun x => x⁻¹) 1 k + 32)]
  have hwhi : fieldWalsh byteCharacter (fun x => x⁻¹) 1 k ≤ 32 := by
    nlinarith [sq_nonneg (fieldWalsh byteCharacter (fun x => x⁻¹) 1 k - 32)]
  have hchi : -1 ≤ byteCharacter k ∧ byteCharacter k ≤ 1 := by
    unfold byteCharacter
    split_ifs <;> norm_num
  rw [inversion_mixed_row_formula k hk, if_neg hk1]
  apply abs_le.mpr
  constructor <;> norm_num <;> linarith [hchi.1, hchi.2]

theorem inversion_mixed_bound (a b : Byte) :
    |kernelCompose inversionGram byteFourierMatrix a b| ≤ (13276 / (4 * 4177920) : ℝ) := by
  have hz (z : Byte) : inversionGram 0 z = if z = 0 then (0 : ℝ) else 0 := by
    simp only [inversion_gram_zero_row, ite_self]
  rw [mixed_product inversionGram 0 hz (inversion_gram_row_sum 1) inversion_gram_scale a b]
  exact inversion_mixed_row_bound (a * b)

/-- Uniform entrywise mixed Fourier resource for each of the four actual
byte residual Grams. Each orientation is fixed throughout its Gram. -/
theorem actual_gram_mixed_bound (o : Orientation) (a b : Byte) :
    |kernelCompose (residualGram (channel o)) byteFourierMatrix a b| ≤
      (13276 / (4 * 4177920) : ℝ) := by
  have hbase : residualGram (channel o) =
      fun y x => inversionGram (gramRelabel o y) (gramRelabel o x) :=
    funext (fun y => funext (actual_gram_relabel o y))
  rw [hbase, mixed_relabel]
  exact inversion_mixed_bound _ _

end AESConcrete.ByteGramMixed
