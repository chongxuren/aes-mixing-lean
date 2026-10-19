import AESConcrete.WordDegreeOperator

/-!
# Assembly of trace and second Gram moment from actual degree HS bounds

This module isolates the remaining quantitative premise: the twenty-five
actual Hilbert--Schmidt degree-block bounds. Operator bounds, orthogonal
decomposition, ideal inequalities and the exact table arithmetic are proved
dependencies. The HS premise is explicit and is not asserted for AES here.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordMomentAssembly
open AESMixing
open ByteOrientations (Orientation)
open WordOrientationClosure (wordKernel)
open DegreeHilbertSchmidt (block block_hs_pythagoras gram_block_identity)
open HilbertSchmidtEnergy (hs hs_sq hs_nonneg)

def residual (left right : Orientation) (inverse : Bool) : AES.Word → AES.Word → ℝ :=
  residualMatrix (wordKernel left right inverse) 0

/-- The missing concrete block resource, with counting-measure HS normalization. -/
def HasDegreeHSBounds (left right : Orientation) (inverse : Bool) : Prop :=
  ∀ i j : Fin 5, hs (block 0 (residual left right inverse) i j) ≤
    WordMomentNumbers.hs i j / 65536

private theorem scaled_min (a b c d : ℝ) :
    min (a/65536*(b/65536)) (c/65536*(d/65536)) =
      min (a*b) (c*d) / 4294967296 := by
  have h1 : a/65536*(b/65536) = a*b/4294967296 := by ring
  have h2 : c/65536*(d/65536) = c*d/4294967296 := by ring
  rw [h1,h2]
  simp only [min_def]
  split_ifs <;> linarith

theorem trace_lt_of_degree_bounds (left right : Orientation) (inverse : Bool)
    (h : HasDegreeHSBounds left right inverse) :
    (∑ y, ∑ x, residual left right inverse y x ^ 2) < 4251 / 4294967296 := by
  rw [← hs_sq, ← block_hs_pythagoras (0 : BinaryWord 8)
    (by norm_num [BinaryWord.card])]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, (WordMomentNumbers.hs i j / 65536)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (hs_nonneg _) (h i j) 2
    _ = (∑ i : Fin 5, ∑ j : Fin 5, WordMomentNumbers.hs i j ^ 2) / 4294967296 := by
      simp only [div_pow]
      norm_num
      simp only [Finset.sum_div]
    _ < _ := div_lt_div_of_pos_right WordMomentNumbers.hs_total_lt (by norm_num)

theorem gram_block_lt_of_degree_bounds (left right : Orientation) (inverse : Bool)
    (h : HasDegreeHSBounds left right inverse) (i j : Fin 5) :
    hs (block 0 (gram (residual left right inverse)) i j) <
      WordMomentNumbers.gramCap i j / 4294967296 := by
  have he : block 0 (gram (residual left right inverse)) i j =
      fun x z => ∑ k : Fin 5, ∑ y, block 0 (residual left right inverse) k i y x *
        block 0 (residual left right inverse) k j y z := by
    funext x z
    exact gram_block_identity 0 (by norm_num [BinaryWord.card]) _ i j x z
  rw [he]
  have hg := HilbertSchmidtEnergy.hs_gram_block_sum_le
    (fun k => block 0 (residual left right inverse) k i)
    (fun k => block 0 (residual left right inverse) k j)
    (fun k => WordMomentNumbers.op k i / 65536)
    (fun k => WordMomentNumbers.op k j / 65536)
    (fun k => WordMomentNumbers.hs k i / 65536)
    (fun k => WordMomentNumbers.hs k j / 65536)
    (fun k => div_nonneg (WordMomentNumbers.op_nonneg k i) (by norm_num))
    (fun k => div_nonneg (WordMomentNumbers.op_nonneg k j) (by norm_num))
    (fun k => WordDegreeOperator.residual_block_table_energy left right inverse k i)
    (fun k => WordDegreeOperator.residual_block_table_energy left right inverse k j)
    (fun k => h k i) (fun k => h k j)
  simp_rw [scaled_min] at hg
  rw [← Finset.sum_div] at hg
  exact hg.trans_lt (div_lt_div_of_pos_right (WordMomentNumbers.gram_row_cap i j)
    (by norm_num))

theorem gram_moment_lt_of_degree_bounds (left right : Orientation) (inverse : Bool)
    (h : HasDegreeHSBounds left right inverse) :
    (∑ x, ∑ z, (∑ y, residual left right inverse y x * residual left right inverse y z)^2) <
      (300 / 4294967296 : ℝ)^2 := by
  change (∑ x, ∑ z, gram (residual left right inverse) x z ^ 2) < _
  rw [← hs_sq]
  rw [← block_hs_pythagoras (0 : BinaryWord 8) (by norm_num [BinaryWord.card])]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, (WordMomentNumbers.gramCap i j / 4294967296)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (hs_nonneg _)
        (le_of_lt (gram_block_lt_of_degree_bounds left right inverse h i j)) 2
    _ = (∑ i : Fin 5, ∑ j : Fin 5, WordMomentNumbers.gramCap i j^2) / 4294967296^2 := by
      simp only [div_pow]
      simp only [Finset.sum_div]
    _ < 90000 / 4294967296^2 := div_lt_div_of_pos_right
      WordMomentNumbers.gram_total_lt (by norm_num)
    _ = _ := by norm_num

end AESConcrete.WordMomentAssembly
