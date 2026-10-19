import AESConcrete.DegreeHilbertSchmidt
import AESConcrete.WordMomentNumbers
import AESConcrete.DegreeCentering

/-!
# Actual centered AES degree-block operator bounds

The earlier directly damped bound assumes centered inputs. Here the actual
residual matrix is used, and the bound holds for every joint input function.
The degree-zero projection commutes with whole-word centering; every positive
degree already has zero distinguished value and zero total mass.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordDegreeOperator
open AESMixing
open ByteOrientations (Orientation)
open WordOrientationClosure (wordKernel word_kernel_pointed)
open DegreeHilbertSchmidt (block block_action)

theorem pointed_residual_commute {V : Type*} [Fintype V] [DecidableEq V]
    {D : V → V → ℝ} {z : V} (h : PointedBistochastic D z) (f : V → ℝ) :
    wordResidual z (action D f) = action D (wordResidual z f) := by
  simp only [wordResidual, action_sub, h.average_action, h.action_average]

theorem degree_idempotent (j : Fin 5) (f : AES.Word → ℝ) :
    degreeComponent 0 j (degreeComponent 0 j f) = degreeComponent 0 j f := by
  simp only [← degreeKernel_action, ← kernelCompose_action,
    degreeKernel_compose (0 : BinaryWord 8) (by norm_num [BinaryWord.card])]

theorem residual_block_l2 (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    l2 (action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f) ≤
      SharpDampedWordNorm.directComparison i j * l2 f := by
  rw [block_action, residualMatrix_action (word_kernel_pointed left right inverse)]
  have hb : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have hw : 1 < Fintype.card AES.Word := by
    norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]
  have hd := SharpDampedWordNorm.directComparison_nonneg i j
  by_cases hj : j = 0
  · subst j
    have hc : wordResidual (0 : AES.Word) (degreeComponent 0 0 f) =
        degreeComponent 0 0 (wordResidual 0 f) := by
      have hp : PointedBistochastic (degreeKernel (0 : BinaryWord 8) 0)
          (0 : AES.Word) := degree_zero_pointed (0 : BinaryWord 8) hb
      simpa only [degreeKernel_action] using pointed_residual_commute hp f
    rw [hc]
    have h := SharpDampedWordNorm.direct_degree_bound left right inverse i 0
      (wordResidual 0 f) (wordResidual_at_zero 0 f) (wordResidual_sum 0 f hw)
    have he := (degreeComponent_energy_le (0 : BinaryWord 8) hb 0 (wordResidual 0 f)).trans
      (residual_energy_le 0 f hw)
    exact h.trans (mul_le_mul_of_nonneg_left
      (l2_le_of_energy _ _ 1 (by norm_num) (by simpa using he) |>.trans_eq (one_mul _)) hd)
  · have hc := DegreeCentering.positive_degree_centered (0 : BinaryWord 8) hb j hj f
    have hz : degreeComponent 0 j f (0 : AES.Word) = 0 := hc.1
    rw [wordResidual_eq_self 0 _ hz hc.2]
    have h := SharpDampedWordNorm.direct_degree_bound left right inverse i j
      (degreeComponent 0 j f) hz hc.2
    rw [degree_idempotent] at h
    have he := degreeComponent_energy_le (0 : BinaryWord 8) hb j f
    exact h.trans (mul_le_mul_of_nonneg_left
      (l2_le_of_energy _ _ 1 (by norm_num) (by simpa using he) |>.trans_eq (one_mul _)) hd)

theorem residual_block_table_l2 (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    l2 (action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f) ≤
      (WordMomentNumbers.op i j / 65536) * l2 f :=
  (residual_block_l2 left right inverse i j f).trans
    (mul_le_mul_of_nonneg_right (WordMomentNumbers.directComparison_le i j) (l2_nonneg f))

theorem residual_block_table_energy (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (f : AES.Word → ℝ) :
    (∑ y, action (block 0 (residualMatrix (wordKernel left right inverse) 0) i j) f y ^ 2) ≤
      (WordMomentNumbers.op i j / 65536)^2 * ∑ x, f x^2 := by
  have hs := mul_self_le_mul_self (l2_nonneg _)
    (residual_block_table_l2 left right inverse i j f)
  simp only [← pow_two] at hs
  simpa only [mul_pow, l2_sq] using hs

end AESConcrete.WordDegreeOperator
