import AES8.Estimates.Word.PaperWordTwoSwapsNumbers
import AES8.Estimates.Word.PaperWordMoments

/-! Literal two-swap assembly of the word second Gram moment.
The original degree HS/operator bounds are used individually; no rounded
per-entry minimum table or assumed word moment is used. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperWordTwoSwaps
open AESMixing AESConcrete
open ByteOrientations (Orientation)
open WordMomentAssembly (residual HasDegreeHSBounds)
open DegreeHilbertSchmidt (block block_hs_pythagoras gram_block_identity)
open HilbertSchmidtEnergy (hs hs_sq hs_nonneg)
open PaperWordTwoSwapsNumbers
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem scaled_min (a b c d : ℝ) :
    min (a/65536*(b/65536)) (c/65536*(d/65536)) =
      min (a*b) (c*d) / 4294967296 := by
  have h1 : a/65536*(b/65536) = a*b/4294967296 := by ring
  have h2 : c/65536*(d/65536) = c*d/4294967296 := by ring
  rw [h1,h2]
  simp only [min_def]
  split_ifs <;> linarith

/-- The actual Gram block obeys the uniform assignment with only two swaps. -/
theorem gram_block_le (left right : Orientation) (inverse : Bool)
    (h : HasDegreeHSBounds left right inverse) (i j : Fin 5) :
    hs (block 0 (gram (residual left right inverse)) i j) ≤
      bound i j / 4294967296 := by
  have he : block 0 (gram (residual left right inverse)) i j =
      fun x z => ∑ k : Fin 5, ∑ y, block 0 (residual left right inverse) k i y x *
        block 0 (residual left right inverse) k j y z := by
    funext x z
    exact gram_block_identity 0 (by norm_num [BinaryWord.card]) _ i j x z
  rw [he]
  have hg := HilbertSchmidtEnergy.hs_gram_block_sum_le
    (fun k => block 0 (residual left right inverse) k i)
    (fun k => block 0 (residual left right inverse) k j)
    (fun k => PaperWordDegreeComparison.comparison k i / 65536)
    (fun k => PaperWordDegreeComparison.comparison k j / 65536)
    (fun k => WordMomentNumbers.hs k i / 65536)
    (fun k => WordMomentNumbers.hs k j / 65536)
    (fun k => div_nonneg (PaperWordDegreeComparison.comparison_nonneg k i) (by norm_num))
    (fun k => div_nonneg (PaperWordDegreeComparison.comparison_nonneg k j) (by norm_num))
    (fun k => PaperWordDegreeComparison.residual_block_energy left right inverse k i)
    (fun k => PaperWordDegreeComparison.residual_block_energy left right inverse k j)
    (fun k => h k i) (fun k => h k j)
  simp_rw [scaled_min] at hg
  rw [← Finset.sum_div] at hg
  exact hg.trans (div_le_div_of_nonneg_right (min_sum_le_bound i j) (by norm_num))

theorem gram_moment_lt_of_degree_bounds (left right : Orientation) (inverse : Bool)
    (h : HasDegreeHSBounds left right inverse) :
    (4294967296 : ℝ)^2 *
      (∑ x, ∑ z, (∑ y, residual left right inverse y x * residual left right inverse y z)^2)
      < 89870 := by
  change (4294967296 : ℝ)^2 * (∑ x, ∑ z, gram (residual left right inverse) x z ^ 2) < _
  rw [← hs_sq, ← block_hs_pythagoras (0 : BinaryWord 8) (by norm_num [BinaryWord.card])]
  have hsum : (∑ i : Fin 5, ∑ j : Fin 5,
      hs (block 0 (gram (residual left right inverse)) i j)^2) ≤
        (∑ i : Fin 5, ∑ j : Fin 5, bound i j ^ 2) / 4294967296^2 := by
    calc
      _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, (bound i j / 4294967296)^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (hs_nonneg _) (gram_block_le left right inverse h i j) 2
      _ = _ := by simp only [div_pow, Finset.sum_div]
  have hp := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4294967296^2)
  have he : (4294967296 : ℝ)^2 *
      ((∑ i : Fin 5, ∑ j : Fin 5, bound i j^2) / 4294967296^2) =
      ∑ i : Fin 5, ∑ j : Fin 5, bound i j^2 := by ring
  rw [he] at hp
  exact hp.trans_lt two_swap_total_lt

/-- The literal paper route on actual AES, both diffusion directions and
independent byte orientations, with all degree bounds discharged. -/
theorem actual_gram_moment_lt (left right : Orientation) (inverse : Bool) :
    (4294967296 : ℝ)^2 *
      (∑ x, ∑ z, (∑ y, residual left right inverse y x * residual left right inverse y z)^2)
      < 89870 :=
  gram_moment_lt_of_degree_bounds left right inverse
    (PaperWordMoments.actual_degree_hs_bounds left right inverse)

end AES8.PaperWordTwoSwaps
