import AES8.Estimates.Byte.PaperByteGramPrinted
import AESConcrete.ByteGramMixed

/-!
# Printed mixed byte Gram entry route

Frozen paper 1906c42e, 10-geometry.tex localres:mixed-kernel. The existing
exact character-sum row identity is reused. Both the ratio-one and other
nonzero-ratio bounds follow only from the stated inversion Walsh premise;
no exact Walsh-at-one value or finite extremal certificate is consumed.
Scalar-product and Fourier relabel identities transport the result.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperByteMixedPrinted
open AESMixing
open AES8.PaperByteGramPrinted (Byte)
open AESConcrete.ByteGramCore (inversionGram inversion_gram_zero_row inversion_gram_row_sum)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteGramFourier
open AESConcrete.ByteOrientations (Orientation channel)
set_option autoImplicit false

/-- The special ratio one uses the same Walsh interval as every other ratio. -/
theorem inversion_mixed_row_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (k : Byte) :
    |kernelCompose inversionGram byteFourierMatrix 1 k| ≤
      (13276 / (4 * 4177920) : ℝ) := by
  by_cases hk : k = 0
  · subst k
    rw [AESConcrete.ByteGramMixed.inversion_mixed_zero]
    norm_num
  have hw := hWalsh 1 k one_ne_zero
  have hwlo : -32 ≤ fieldWalsh byteCharacter (fun x => x⁻¹) 1 k := by
    nlinarith [sq_nonneg (fieldWalsh byteCharacter (fun x => x⁻¹) 1 k + 32)]
  have hwhi : fieldWalsh byteCharacter (fun x => x⁻¹) 1 k ≤ 32 := by
    nlinarith [sq_nonneg (fieldWalsh byteCharacter (fun x => x⁻¹) 1 k - 32)]
  rw [AESConcrete.ByteGramMixed.inversion_mixed_row_formula k hk]
  by_cases hk1 : k = 1
  · subst k
    rw [if_pos rfl, AES8.PaperByteGramPrinted.character_one]
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith
  · have hchi : -1 ≤ byteCharacter k ∧ byteCharacter k ≤ 1 := by
      unfold byteCharacter
      split_ifs <;> norm_num
    rw [if_neg hk1]
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith [hchi.1, hchi.2]

theorem inversion_mixed_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (a b : Byte) :
    |kernelCompose inversionGram byteFourierMatrix a b| ≤
      (13276 / (4 * 4177920) : ℝ) := by
  have hz (z : Byte) : inversionGram 0 z = if z = 0 then (0 : ℝ) else 0 := by
    simp only [inversion_gram_zero_row, ite_self]
  rw [mixed_product inversionGram 0 hz (inversion_gram_row_sum 1) inversion_gram_scale a b]
  exact inversion_mixed_row_bound_of_walsh hWalsh (a * b)

theorem actual_gram_mixed_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (o : Orientation) (a b : Byte) :
    |kernelCompose (residualGram (channel o)) byteFourierMatrix a b| ≤
      (13276 / (4 * 4177920) : ℝ) := by
  have hbase : residualGram (channel o) =
      fun y x => inversionGram (gramRelabel o y) (gramRelabel o x) :=
    funext (fun y => funext (actual_gram_relabel o y))
  rw [hbase, mixed_relabel]
  exact inversion_mixed_bound_of_walsh hWalsh _ _

/-- Concrete provider is separate from the printed conditional deduction. -/
theorem actual_gram_mixed_bound (o : Orientation) (a b : Byte) :
    |kernelCompose (residualGram (channel o)) byteFourierMatrix a b| ≤
      (13276 / (4 * 4177920) : ℝ) :=
  actual_gram_mixed_bound_of_walsh PaperCitedByteBounds.concreteWalshBound o a b

#print axioms inversion_mixed_row_bound_of_walsh
#print axioms inversion_mixed_bound_of_walsh
#print axioms actual_gram_mixed_bound_of_walsh
#print axioms actual_gram_mixed_bound
end AES8.PaperByteMixedPrinted
