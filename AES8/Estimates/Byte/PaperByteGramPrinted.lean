import AES8.Math.PaperSignPairCounts
import AES8.Model.PaperByteTrace
import AES8.Estimates.Byte.PaperCitedByteBounds

/-!
The printed byte second-moment route, paper commit 1906c42e:
Walsh -> Kloosterman -> four trace cells -> H <= 70 -> row-square energy.

Only the exact n=8 inversion Walsh bound is a numerical input. The inherited
inversion Gram formula, its zero row, and the exact AES orientation relabeling
are identities used at their stated interfaces. No exact H=70 enumeration,
finite numerator sum or inherited Gram-moment estimate supplies this proof.
Concrete providers and the final paper-facing consumer remain separate.
Source-only candidate; no attacks, vendor/manuscript edits or local execution.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperByteGramPrinted
open AESMixing PaperByteTrace PaperSignPairCounts
open AESConcrete.ByteGramCore (inversionGram inversion_gram_nonzero
  inversion_gram_zero_row inversion_gram_zero_column)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteGramFourier (actual_gram_relabel gramRelabel)
open AESConcrete.ByteOrientations (Orientation channel)
set_option autoImplicit false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

abbrev Byte := BinaryWord 8
abbrev NonzeroByte := {x : Byte // x ≠ 0}

/-- Exactly the paper's off-diagonal ratio labels. -/
def offDiagonal : Finset Byte := (Finset.univ.erase 0).erase 1

theorem mem_offDiagonal (c : Byte) : c ∈ offDiagonal ↔ c ≠ 0 ∧ c ≠ 1 := by
  simp [offDiagonal, and_comm]

theorem sum_offDiagonal (f : Byte → ℝ) :
    (∑ c ∈ offDiagonal, f c) = (∑ c, f c) - f 0 - f 1 := by
  have h0 : (∑ c ∈ (Finset.univ : Finset Byte).erase 0, f c) + f 0 =
      ∑ c : Byte, f c := Finset.sum_erase_add _ _ (by simp)
  have h1 : (∑ c ∈ offDiagonal, f c) + f 1 =
      ∑ c ∈ (Finset.univ : Finset Byte).erase 0, f c := by
    exact Finset.sum_erase_add _ _ (by simp)
  linarith

theorem offDiagonal_card : (offDiagonal.card : ℝ) = 254 := by
  have h := sum_offDiagonal (fun _ => (1 : ℝ))
  norm_num only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    BinaryWord.card] at h
  exact h

theorem character_one : byteCharacter (1 : Byte) = 1 := by rfl

theorem character_cases (c : Byte) : byteCharacter c = 1 ∨ byteCharacter c = -1 := by
  unfold byteCharacter
  split_ifs <;> simp

theorem character_eq_one_iff_trace (c : Byte) :
    byteCharacter c = 1 ↔ absoluteTrace c = 0 := by
  rw [← traceCharacter_eq]
  unfold traceCharacter
  split_ifs with h <;> norm_num [h]

/-- Both zero-trace conditions, counted as a natural integer H. -/
def traceCell (u v : ℝ) : ℕ :=
  cellCount offDiagonal byteCharacter (fun c => byteCharacter c⁻¹) u v

def H : ℕ := traceCell 1 1

theorem H_eq_trace_count : H =
    ∑ c ∈ offDiagonal, if absoluteTrace c = 0 ∧ absoluteTrace c⁻¹ = 0 then 1 else 0 := by
  simp only [H, traceCell, cellCount, character_eq_one_iff_trace]

def kloosterman (z : Byte) : ℝ :=
  ∑ x : NonzeroByte, traceCharacter (x.val + z/x.val)

theorem kloosterman_eq_walsh (z : Byte) :
    kloosterman z = fieldWalsh byteCharacter (fun x => x⁻¹) 1 z - 1 := by
  unfold fieldWalsh
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun x : Byte => byteCharacter (1*x+z*x⁻¹)) 0]
  simp only [mul_zero, inv_zero, add_zero, byteCharacter_zero, one_mul]
  unfold kloosterman
  simp only [traceCharacter_eq, div_eq_mul_inv]
  ring

theorem kloosterman_bounds_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (z : Byte) :
    -33 ≤ kloosterman z ∧ kloosterman z ≤ 31 := by
  rw [kloosterman_eq_walsh]
  have h := hWalsh 1 z one_ne_zero
  constructor <;> nlinarith

theorem first_sign_sum : (∑ c ∈ offDiagonal, byteCharacter c) = -2 := by
  have h := sum_offDiagonal byteCharacter
  rw [byteCharacter_sum, byteCharacter_zero, character_one] at h
  norm_num at h
  exact h

theorem second_sign_sum : (∑ c ∈ offDiagonal, byteCharacter c⁻¹) = -2 := by
  have hall : (∑ c : Byte, byteCharacter c⁻¹) = 0 := by
    have h := Equiv.sum_comp (invPermutation (F := Byte)) byteCharacter
    change (∑ c : Byte, byteCharacter c⁻¹) = ∑ c : Byte, byteCharacter c at h
    exact h.trans byteCharacter_sum
  have h := sum_offDiagonal (fun c => byteCharacter c⁻¹)
  rw [hall, inv_zero, inv_one, byteCharacter_zero, character_one] at h
  norm_num at h
  exact h

theorem product_sign_sum :
    (∑ c ∈ offDiagonal, byteCharacter c * byteCharacter c⁻¹) = kloosterman 1 - 1 := by
  have h := sum_offDiagonal (fun c => byteCharacter c * byteCharacter c⁻¹)
  rw [inv_zero, inv_one, byteCharacter_zero, character_one] at h
  have hk := kloosterman_eq_walsh 1
  simp only [fieldWalsh, one_mul, byteCharacter_add] at hk
  linarith

/-- The two single-zero cells have size126-H and the no-zero cell H+2.
Counts are natural integers; the displayed formulas use their real casts. -/
theorem four_cell_histogram :
    (traceCell 1 (-1) : ℝ) = 126 - (H : ℝ) ∧
    (traceCell (-1) 1 : ℝ) = 126 - (H : ℝ) ∧
    (traceCell (-1) (-1) : ℝ) = (H : ℝ) + 2 ∧
    kloosterman 1 = 4*(H : ℝ) - 249 := by
  have hp := four_times_count offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    1 1 (Or.inl rfl) (Or.inl rfl)
  have hpm := four_times_count offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    1 (-1) (Or.inl rfl) (Or.inr rfl)
  have hmp := four_times_count offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have hm := four_times_count offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  change 4*(H : ℝ) = _ at hp
  change 4*(traceCell 1 (-1) : ℝ) = _ at hpm
  change 4*(traceCell (-1) 1 : ℝ) = _ at hmp
  change 4*(traceCell (-1) (-1) : ℝ) = _ at hm
  rw [offDiagonal_card, first_sign_sum, second_sign_sum, product_sign_sum] at hp hpm hmp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- This is the printed H<=70 deduction, with no exact-count premise. -/
theorem H_le_seventy (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) : H ≤ 70 := by
  have hk := (kloosterman_bounds_of_walsh hWalsh 1).2
  have he := four_cell_histogram.2.2.2
  have hreal : (H : ℝ) ≤ 70 := by linarith
  exact_mod_cast hreal

def rowNumerator (h : ℝ) : ℝ :=
  16766^2 + h*191^2 + (252-2*h)*64^2 + (h+2)*319^2

theorem offDiagonal_square_sum :
    (∑ c ∈ offDiagonal,
      (-64 + (255/2 : ℝ)*(byteCharacter c + byteCharacter c⁻¹))^2) =
      (H : ℝ)*191^2 + (252-2*(H : ℝ))*64^2 + ((H : ℝ)+2)*319^2 := by
  have hs := square_sum offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    (-64) (255/2)
  change _ = (-64+2*(255/2 : ℝ))^2*(H : ℝ) + (-64 : ℝ)^2 *
    ((traceCell 1 (-1) : ℝ)+(traceCell (-1) 1 : ℝ)) +
    (-64-2*(255/2 : ℝ))^2*(traceCell (-1) (-1) : ℝ) at hs
  rw [four_cell_histogram.1, four_cell_histogram.2.1, four_cell_histogram.2.2.1] at hs
  calc
    _ = (-64+2*(255/2 : ℝ))^2*(H : ℝ) + (-64 : ℝ)^2 *
        ((126-(H : ℝ))+(126-(H : ℝ))) +
        (-64-2*(255/2 : ℝ))^2*((H : ℝ)+2) := hs
    _ = _ := by ring

theorem inversion_diagonal (a : Byte) (ha : a ≠ 0) :
    inversionGram a a = 16766/4177920 := by
  rw [inversion_gram_nonzero a a ha ha]
  simp only [if_pos rfl, div_self ha, character_one]
  norm_num

/-- Multiplicative ratios give the exact three-valued off-diagonal profile. -/
theorem inversion_offDiagonal_ratio (a c : Byte)
    (ha : a ≠ 0) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    inversionGram a (a*c) =
      (-64 + (255/2 : ℝ)*(byteCharacter c + byteCharacter c⁻¹)) / 4177920 := by
  have hne : a ≠ a*c := by
    intro h
    apply hc1
    apply mul_left_cancel₀ ha
    simpa only [mul_one] using h.symm
  have hr1 : a/(a*c) = c⁻¹ := by field_simp [ha, hc0]
  have hr2 : (a*c)/a = c := by field_simp [ha]
  rw [inversion_gram_nonzero a (a*c) ha (mul_ne_zero ha hc0), if_neg hne, hr1, hr2]
  ring

/-- One diagonal plus the four-cell off-diagonal square sum. -/
theorem inversion_row_square (a : Byte) (ha : a ≠ 0) :
    (∑ b, inversionGram a b^2) = rowNumerator (H : ℝ) / 4177920^2 := by
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => inversionGram a b^2)
  have hsplit := sum_offDiagonal (fun c => inversionGram a (a*c)^2)
  have hoff : (∑ c ∈ offDiagonal, inversionGram a (a*c)^2) =
      ∑ c ∈ offDiagonal,
        ((-64+(255/2 : ℝ)*(byteCharacter c+byteCharacter c⁻¹))/4177920)^2 := by
    apply Finset.sum_congr rfl
    intro c hc
    rcases (mem_offDiagonal c).mp hc with ⟨hc0,hc1⟩
    rw [inversion_offDiagonal_ratio a c ha hc0 hc1]
  rw [hoff] at hsplit
  simp only [mul_zero, inversion_gram_zero_column, zero_pow (by decide : 2 ≠ 0),
    mul_one, inversion_diagonal a ha] at hsplit
  simp_rw [div_pow] at hsplit
  rw [← Finset.sum_div, offDiagonal_square_sum] at hsplit
  change (∑ c : Byte, inversionGram a (a*c)^2) = ∑ b : Byte, inversionGram a b^2 at he
  rw [← he]
  unfold rowNumerator
  linarith only [hsplit]

/-- The zero row contributes0 and the other255 rows have identical energy. -/
theorem inversion_moment_formula :
    (∑ a, ∑ b, inversionGram a b^2) =
      255 * rowNumerator (H : ℝ) / 4177920^2 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => ∑ b, inversionGram a b^2) 0]
  simp only [inversion_gram_zero_row, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add]
  have hr (a : NonzeroByte) : (∑ b, inversionGram a.val b^2) =
      rowNumerator (H : ℝ) / 4177920^2 := inversion_row_square a.val a.property
  simp_rw [hr]
  have hn : (∑ _ : NonzeroByte, (1 : ℝ)) = 255 := by
    norm_num [NonzeroByte, BinaryWord.card]
  calc
    _ = (∑ _ : NonzeroByte, (1 : ℝ)) * (rowNumerator (H : ℝ)/4177920^2) := by
      rw [Finset.sum_mul]
      simp only [one_mul]
    _ = _ := by rw [hn]; ring

theorem rowNumerator_le {h : ℝ} (hh : h ≤ 70) : rowNumerator h ≤ rowNumerator 70 := by
  unfold rowNumerator
  nlinarith

/-- The paper's second-moment bound follows by monotonicity in H. -/
theorem inversion_moment_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) :
    (∑ a, ∑ b, inversionGram a b^2) ≤ (571447 / 2^27 : ℝ) := by
  rw [inversion_moment_formula]
  have hh : (H : ℝ) ≤ 70 := by exact_mod_cast H_le_seventy hWalsh
  calc
    _ ≤ 255 * rowNumerator 70 / 4177920^2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (rowNumerator_le hh) (by norm_num)
    _ = _ := by norm_num [rowNumerator]

/-- Exact relabeling transports the printed bound to all four actual Grams. -/
theorem actual_gram_square_moment_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) :
    (∑ a, ∑ b, residualGram (channel o) a b^2) ≤ (571447 / 2^27 : ℝ) := by
  simp_rw [actual_gram_relabel]
  have hi (a : Byte) :
      (∑ b, inversionGram (gramRelabel o a) (gramRelabel o b)^2) =
        ∑ b, inversionGram (gramRelabel o a) b^2 :=
    Equiv.sum_comp (gramRelabel o).toEquiv (fun b => inversionGram (gramRelabel o a) b^2)
  simp_rw [hi]
  have ho := Equiv.sum_comp (gramRelabel o).toEquiv
    (fun a => ∑ b, inversionGram a b^2)
  exact ho.le.trans (inversion_moment_le_of_walsh hWalsh)

/-- Existing concrete provider; the displayed proof chain remains explicit. -/
theorem actual_gram_square_moment_le (o : Orientation) :
    (∑ a, ∑ b, residualGram (channel o) a b^2) ≤ (571447 / 2^27 : ℝ) :=
  actual_gram_square_moment_le_of_walsh PaperCitedByteBounds.concreteWalshBound o

#print axioms four_cell_histogram
#print axioms H_le_seventy
#print axioms inversion_row_square
#print axioms inversion_moment_formula
#print axioms inversion_moment_le_of_walsh
#print axioms actual_gram_square_moment_le_of_walsh
#print axioms actual_gram_square_moment_le
end AES8.PaperByteGramPrinted
