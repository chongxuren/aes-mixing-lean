import AES8.Math.PaperSignPairWeights
import AES8.Estimates.Byte.PaperByteGramPrinted

/-!
# Printed absolute cubic byte Gram route

Frozen paper 1906c42e, 10-geometry.tex localres:cubic. The exact symbolic
four-cell histogram yields the H-dependent absolute cube. Its coefficient
of H is positive, so the accepted inversion Walsh premise gives H <= 70
and the printed upper bound. No exact H=70 or finite cube sum is a premise.
Orientation relabeling and concrete input providers remain explicit.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperByteCubePrinted
open AESMixing
open AES8.PaperByteGramPrinted
open AES8.PaperSignPairCounts
open AESConcrete.ByteGramCore (inversionGram inversion_gram_zero_row inversion_gram_zero_column)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteGramFourier (actual_gram_relabel gramRelabel)
open AESConcrete.ByteOrientations (Orientation channel)
set_option autoImplicit false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- One diagonal plus the absolute cubic weights of the symbolic cells. -/
def cubeRowNumerator (h : ℝ) : ℝ :=
  16766^3 + h*191^3 + (252-2*h)*64^3 + (h+2)*319^3

theorem offDiagonal_absolute_cube_sum :
    (∑ c ∈ offDiagonal,
      |(-64 : ℝ) + (255/2 : ℝ)*(byteCharacter c + byteCharacter c⁻¹)|^3) =
      (H : ℝ)*191^3 + (252-2*(H : ℝ))*64^3 + ((H : ℝ)+2)*319^3 := by
  have hs := AES8.PaperSignPairWeights.weighted_sum
    offDiagonal byteCharacter (fun c => byteCharacter c⁻¹)
    (fun c _ => character_cases c) (fun c _ => character_cases c⁻¹)
    (fun u v => |(-64 : ℝ)+(255/2 : ℝ)*(u+v)|^3)
  change _ = |(-64 : ℝ)+(255/2 : ℝ)*(1+1)|^3*(H : ℝ) +
    |(-64 : ℝ)+(255/2 : ℝ)*(1+(-1))|^3*(traceCell 1 (-1) : ℝ) +
    |(-64 : ℝ)+(255/2 : ℝ)*((-1)+1)|^3*(traceCell (-1) 1 : ℝ) +
    |(-64 : ℝ)+(255/2 : ℝ)*((-1)+(-1))|^3*(traceCell (-1) (-1) : ℝ) at hs
  rw [four_cell_histogram.1, four_cell_histogram.2.1, four_cell_histogram.2.2.1] at hs
  norm_num at hs ⊢
  linarith only [hs]

/-- Multiplicative ratios transport the symbolic cubic cell sum to each row. -/
theorem inversion_row_absolute_cube (a : Byte) (ha : a ≠ 0) :
    (∑ b, |inversionGram a b|^3) = cubeRowNumerator (H : ℝ) / 4177920^3 := by
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => |inversionGram a b|^3)
  have hsplit := sum_offDiagonal (fun c => |inversionGram a (a*c)|^3)
  have hoff : (∑ c ∈ offDiagonal, |inversionGram a (a*c)|^3) =
      ∑ c ∈ offDiagonal,
        |((-64+(255/2 : ℝ)*(byteCharacter c+byteCharacter c⁻¹))/4177920)|^3 := by
    apply Finset.sum_congr rfl
    intro c hc
    rcases (mem_offDiagonal c).mp hc with ⟨hc0,hc1⟩
    rw [inversion_offDiagonal_ratio a c ha hc0 hc1]
  rw [hoff] at hsplit
  simp only [mul_zero, inversion_gram_zero_column, abs_zero,
    zero_pow (by decide : 3 ≠ 0), mul_one, inversion_diagonal a ha] at hsplit
  simp_rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4177920), div_pow] at hsplit
  rw [← Finset.sum_div, offDiagonal_absolute_cube_sum] at hsplit
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 16766)] at hsplit
  change (∑ c : Byte, |inversionGram a (a*c)|^3) =
    ∑ b : Byte, |inversionGram a b|^3 at he
  rw [← he]
  unfold cubeRowNumerator
  linarith only [hsplit]

/-- The zero row vanishes and the other 255 rows have the same cubic sum. -/
theorem inversion_absolute_cube_formula :
    (∑ a, ∑ b, |inversionGram a b|^3) =
      255 * cubeRowNumerator (H : ℝ) / 4177920^3 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => ∑ b, |inversionGram a b|^3) 0]
  simp only [inversion_gram_zero_row, abs_zero, zero_pow (by decide : 3 ≠ 0),
    Finset.sum_const_zero, zero_add]
  have hr (a : NonzeroByte) : (∑ b, |inversionGram a.val b|^3) =
      cubeRowNumerator (H : ℝ) / 4177920^3 := inversion_row_absolute_cube a.val a.property
  simp_rw [hr]
  have hn : (∑ _ : NonzeroByte, (1 : ℝ)) = 255 := by
    norm_num [NonzeroByte, BinaryWord.card]
  calc
    _ = (∑ _ : NonzeroByte, (1 : ℝ)) * (cubeRowNumerator (H : ℝ)/4177920^3) := by
      rw [Finset.sum_mul]
      simp only [one_mul]
    _ = _ := by rw [hn]; ring

theorem cubeRowNumerator_le {h : ℝ} (hh : h ≤ 70) :
    cubeRowNumerator h ≤ cubeRowNumerator 70 := by
  unfold cubeRowNumerator
  nlinarith

theorem inversion_absolute_cube_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) :
    (∑ a, ∑ b, |inversionGram a b|^3) ≤
      (255 : ℝ)*(16766^3+70*191^3+112*64^3+72*319^3)/4177920^3 := by
  rw [inversion_absolute_cube_formula]
  have hh : (H : ℝ) ≤ 70 := by exact_mod_cast H_le_seventy hWalsh
  calc
    _ ≤ 255 * cubeRowNumerator 70 / 4177920^3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (cubeRowNumerator_le hh) (by norm_num)
    _ = _ := by norm_num [cubeRowNumerator]

theorem actual_gram_absolute_cube_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) :
    (∑ a, ∑ b, |residualGram (channel o) a b|^3) ≤
      (255 : ℝ)*(16766^3+70*191^3+112*64^3+72*319^3)/4177920^3 := by
  simp_rw [actual_gram_relabel]
  have hi (a : Byte) :
      (∑ b, |inversionGram (gramRelabel o a) (gramRelabel o b)|^3) =
        ∑ b, |inversionGram (gramRelabel o a) b|^3 :=
    Equiv.sum_comp (gramRelabel o).toEquiv (fun b => |inversionGram (gramRelabel o a) b|^3)
  simp_rw [hi]
  have ho := Equiv.sum_comp (gramRelabel o).toEquiv
    (fun a => ∑ b, |inversionGram a b|^3)
  exact ho.le.trans (inversion_absolute_cube_le_of_walsh hWalsh)

/-- Concrete provider is separate from the printed conditional deduction. -/
theorem actual_gram_absolute_cube_le (o : Orientation) :
    (∑ a, ∑ b, |residualGram (channel o) a b|^3) ≤
      (255 : ℝ)*(16766^3+70*191^3+112*64^3+72*319^3)/4177920^3 :=
  actual_gram_absolute_cube_le_of_walsh PaperCitedByteBounds.concreteWalshBound o

#print axioms offDiagonal_absolute_cube_sum
#print axioms inversion_row_absolute_cube
#print axioms inversion_absolute_cube_formula
#print axioms inversion_absolute_cube_le_of_walsh
#print axioms actual_gram_absolute_cube_le_of_walsh
#print axioms actual_gram_absolute_cube_le
end AES8.PaperByteCubePrinted
