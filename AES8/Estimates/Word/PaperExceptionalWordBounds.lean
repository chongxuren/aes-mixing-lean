import AES8.Estimates.Word.PaperExceptionalWordEntries
import AES8.Estimates.Word.OneSidedFourthAggregation
import AES8.Estimates.Byte.ByteExceptionalEnvelope

/-!
# Actual exceptional one-sided word fourth moments

The exceptional support consists of literal one-active-byte word labels.
Its parametrization is injective, giving exactly 1020 labels. Each selected
row and column consists of four physical byte-position blocks. The concrete
entry identity instantiates the byte convex-envelope theorem on each block,
through its printed 1623000 intermediate and the scaled 25 * 2^44 allowance.
The remaining nonexceptional entry cap is a separate resource.
Constructive only; no attacks, manuscript changes or proof bypasses.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperExceptionalWordBounds
open AESMixing
open AESConcrete.ByteGramCore (NonzeroByte)
open AESConcrete.WordColumnGram (singleByteWord)
open AESConcrete.SingleByteCoordinates (coordinatePerm)
open AESConcrete.WordFourierVariants (baseOrientation)
open AES8.OneSidedWordEnergy (rightMixed)
open AES8.PaperExceptionalWordEntries

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Every physical position block has the paper's scaled row cap. -/
theorem scaled_block_row_lt (adjoint : Bool) (j k : Fin 4) (b : NonzeroByte) :
    (∑ a : NonzeroByte,
      ((4294967296 : ℝ) * rightMixed adjoint
        (singleByteWord j b.val) (singleByteWord k a.val)) ^ 4) < 25 * 2 ^ 44 := by
  simp_rw [rightMixed_single_entry]
  exact AES8.ByteExceptionalEnvelope.scaled_row_fourth_lt
    (baseOrientation adjoint) (baseOrientation adjoint)
    (coordinatePerm (!adjoint) j k) b.val translation translation_nonneg translation_le

/-- Every physical position block has the paper's scaled column cap. -/
theorem scaled_block_column_lt (adjoint : Bool) (j k : Fin 4) (a : NonzeroByte) :
    (∑ b : NonzeroByte,
      ((4294967296 : ℝ) * rightMixed adjoint
        (singleByteWord j b.val) (singleByteWord k a.val)) ^ 4) < 25 * 2 ^ 44 := by
  simp_rw [rightMixed_single_entry]
  exact AES8.ByteExceptionalEnvelope.scaled_column_fourth_lt
    (baseOrientation adjoint) (baseOrientation adjoint)
    (coordinatePerm (!adjoint) j k) a.val translation translation_nonneg translation_le

theorem block_row_lt (adjoint : Bool) (j k : Fin 4) (b : NonzeroByte) :
    (∑ a : NonzeroByte,
      rightMixed adjoint (singleByteWord j b.val) (singleByteWord k a.val) ^ 4) <
        (25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
  have h := scaled_block_row_lt adjoint j k b
  simp only [mul_pow, ← Finset.mul_sum] at h
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4294967296 ^ 4)).mpr
    (by simpa only [mul_comm] using h)

theorem block_column_lt (adjoint : Bool) (j k : Fin 4) (a : NonzeroByte) :
    (∑ b : NonzeroByte,
      rightMixed adjoint (singleByteWord j b.val) (singleByteWord k a.val) ^ 4) <
        (25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
  have h := scaled_block_column_lt adjoint j k a
  simp only [mul_pow, ← Finset.mul_sum] at h
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4294967296 ^ 4)).mpr
    (by simpa only [mul_comm] using h)

def singleLabel (p : Fin 4 × NonzeroByte) : AES.Word := singleByteWord p.1 p.2.val

theorem singleLabel_injective : Function.Injective singleLabel := by
  intro p r h
  have hk : p.1 = r.1 := by
    by_contra hne
    have he := congrFun h p.1
    have hz : p.2.val = 0 := by simpa [singleLabel, singleByteWord, hne] using he
    exact p.2.property hz
  apply Prod.ext hk
  apply Subtype.ext
  have he := congrFun h p.1
  simpa [singleLabel, singleByteWord, hk] using he

def oneActiveWords : Finset AES.Word := Finset.univ.image singleLabel

theorem oneActiveWords_card : oneActiveWords.card = 1020 := by
  rw [oneActiveWords, Finset.card_image_of_injective _ singleLabel_injective,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    AES8.ByteExceptionalBlockResources.nonzero_card]

theorem mem_oneActiveWords (y : AES.Word) :
    y ∈ oneActiveWords ↔ ∃ j : Fin 4, ∃ b : NonzeroByte, singleByteWord j b.val = y := by
  simp only [oneActiveWords, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, singleLabel]

/-- The enumeration agrees with the literal one-nonzero-coordinate predicate
used by the separately proved nonexceptional entry cap. -/
theorem mem_oneActiveWords_iff_support (y : AES.Word) :
    y ∈ oneActiveWords ↔
      ∃ j : Fin 4, y j ≠ 0 ∧ ∀ i : Fin 4, i ≠ j → y i = 0 := by
  rw [mem_oneActiveWords]
  constructor
  · rintro ⟨j, b, rfl⟩
    refine ⟨j, ?_, ?_⟩
    · simpa [singleByteWord] using b.property
    · intro i hi
      simp [singleByteWord, hi]
  · rintro ⟨j, hj, hs⟩
    refine ⟨j, ⟨y j, hj⟩, ?_⟩
    funext i
    by_cases hi : i = j
    · subst i
      simp [singleByteWord]
    · simp [singleByteWord, hi, hs i hi]

theorem sum_oneActiveWords (f : AES.Word → ℝ) :
    (∑ x ∈ oneActiveWords, f x) =
      ∑ k : Fin 4, ∑ a : NonzeroByte, f (singleByteWord k a.val) := by
  rw [oneActiveWords, Finset.sum_image
    (fun p _ r _ h => singleLabel_injective h), Fintype.sum_prod_type]
  rfl

/-- Exceptional columns of a row. Both labels must have one active byte. -/
def exceptionalInputs (y : AES.Word) : Finset AES.Word :=
  if y ∈ oneActiveWords then oneActiveWords else ∅

theorem mem_exceptionalInputs (y x : AES.Word) :
    x ∈ exceptionalInputs y ↔ y ∈ oneActiveWords ∧ x ∈ oneActiveWords := by
  by_cases hy : y ∈ oneActiveWords <;> simp [exceptionalInputs, hy]

theorem exceptionalInputs_symmetric (y x : AES.Word) :
    x ∈ exceptionalInputs y ↔ y ∈ exceptionalInputs x := by
  rw [mem_exceptionalInputs, mem_exceptionalInputs, and_comm]

theorem row_exceptional_le (adjoint : Bool) (y : AES.Word) :
    (∑ x ∈ exceptionalInputs y, rightMixed adjoint y x ^ 4) ≤
      (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
  by_cases hy : y ∈ oneActiveWords
  · rw [exceptionalInputs, if_pos hy, sum_oneActiveWords]
    obtain ⟨j, b, rfl⟩ := (mem_oneActiveWords y).mp hy
    calc
      _ ≤ ∑ k : Fin 4, (25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact (block_row_lt adjoint j k b).le
      _ = _ := by norm_num
  · rw [exceptionalInputs, if_neg hy, Finset.sum_empty]
    positivity

theorem column_exceptional_le (adjoint : Bool) (x : AES.Word) :
    (∑ y ∈ exceptionalInputs x, rightMixed adjoint y x ^ 4) ≤
      (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
  by_cases hx : x ∈ oneActiveWords
  · rw [exceptionalInputs, if_pos hx, sum_oneActiveWords]
    obtain ⟨k, a, rfl⟩ := (mem_oneActiveWords x).mp hx
    calc
      _ ≤ ∑ j : Fin 4, (25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact (block_column_lt adjoint j k a).le
      _ = _ := by norm_num
  · rw [exceptionalInputs, if_neg hx, Finset.sum_empty]
    positivity

theorem total_exceptional_le (adjoint : Bool) :
    (∑ y : AES.Word, ∑ x ∈ exceptionalInputs y, rightMixed adjoint y x ^ 4) ≤
      (1020 * (4 * 25 * 2 ^ 44) / 4294967296 ^ 4 : ℝ) := by
  have hs : (∑ y : AES.Word, ∑ x ∈ exceptionalInputs y, rightMixed adjoint y x ^ 4) =
      ∑ y ∈ oneActiveWords, ∑ x ∈ exceptionalInputs y, rightMixed adjoint y x ^ 4 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    simp [exceptionalInputs, hy]
  rw [hs]
  calc
    _ ≤ ∑ _y ∈ oneActiveWords, (4 * 25 * 2 ^ 44 / 4294967296 ^ 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro y _
      exact row_exceptional_le adjoint y
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, oneActiveWords_card]; norm_num

-- These corollaries leave only the ordinary entry cap, separately owned by
-- the nonexceptional byte/MDS calculation. The exceptional resources are actual.
theorem row_fourth_lt (adjoint : Bool) (y : AES.Word)
    (hentry : ∀ x, x ∉ exceptionalInputs y →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ)) :
    (∑ x, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) :=
  AES8.OneSidedFourthAggregation.row_fourth_lt adjoint y (exceptionalInputs y)
    hentry (row_exceptional_le adjoint y)

theorem column_fourth_lt (adjoint : Bool) (x : AES.Word)
    (hentry : ∀ y, y ∉ exceptionalInputs x →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ)) :
    (∑ y, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) :=
  AES8.OneSidedFourthAggregation.column_fourth_lt adjoint x (exceptionalInputs x)
    hentry (column_exceptional_le adjoint x)

theorem total_fourth_lt (adjoint : Bool)
    (hentry : ∀ y x, x ∉ exceptionalInputs y →
      |rightMixed adjoint y x| ≤ (1152 / 4294967296 : ℝ)) :
    (∑ y, ∑ x, rightMixed adjoint y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) :=
  AES8.OneSidedFourthAggregation.total_fourth_lt adjoint exceptionalInputs
    hentry (total_exceptional_le adjoint)

end AES8.PaperExceptionalWordBounds
