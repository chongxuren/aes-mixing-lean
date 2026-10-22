import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Estimates.Word.PaperExceptionalWordFourth
import AES8.Estimates.Word.PaperWordMixedGram
import AES8.Estimates.Word.PaperWordTraceVariants

/-!
# Fourth moments for every independent word Fourier choice

The simultaneous Fourier variants use their sharper entry cap. The two
one-sided choices use the actual exceptional-block theorem; left Fourier
multiplication is the transpose of right multiplication with the opposite
adjoint flag. This supplies the three fourth-moment resources on the literal
mixed kernels used by the graph estimates. Equal Fourier flags use the proved
46/q entry cap here; the sharper paper 27/q entry resource is separate.
Constructive only; no attacks, manuscript changes or proof bypasses.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperExceptionalWordVariants
open AESMixing
open AESConcrete.WordFourierCore
open AESConcrete.WordFourierVariants
open AES8.OneSidedWordEnergy (rightMixed baseResidual_transpose)
open AES8.PaperWordMixedGram (mixed)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

theorem mixed_same_flags (adjoint fourier : Bool) :
    mixed adjoint fourier fourier = variant adjoint fourier := by
  cases fourier <;> simp only [variant, mixed, Bool.false_eq_true, if_false, if_true,
    wordConjugate, fourierConjugate, wordFourier]

theorem mixed_left_transpose (adjoint : Bool) (y x : AES.Word) :
    mixed adjoint true false y x = rightMixed (!adjoint) x y := by
  unfold mixed rightMixed kernelCompose
  simp only [Bool.false_eq_true, if_false, if_true, baseResidual_transpose]
  apply Finset.sum_congr rfl
  intro z _
  rw [wordFourier_symmetric y z]
  ring

private theorem fourth_le_square {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (hentry : ∀ i, |f i| ≤ (46 / 4294967296 : ℝ)) :
    (∑ i, f i ^ 4) ≤ (46 / 4294967296 : ℝ) ^ 2 * (∑ i, f i ^ 2) := by
  have h := AES8.OneSidedFourthAggregation.fourth_sum_le_of_exceptional
    f ∅ (46 / 4294967296) 0 (by norm_num)
    (fun i _ => hentry i) (by simp)
  simpa only [add_zero] using h

theorem variant_row_fourth_lt (adjoint fourier : Bool) (y : AES.Word) :
    (∑ x, variant adjoint fourier y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  have he := AES8.PaperWordMixedGram.mixed_row_energy_lt adjoint fourier fourier y
  rw [mixed_same_flags] at he
  calc
    _ ≤ (46 / 4294967296 : ℝ) ^ 2 * (∑ x, variant adjoint fourier y x ^ 2) :=
      fourth_le_square _ (fun x => (variant_entry_lt adjoint fourier x y).le)
    _ < (46 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) :=
      mul_lt_mul_of_pos_left he (by norm_num)
    _ < _ := by norm_num

theorem variant_column_fourth_lt (adjoint fourier : Bool) (x : AES.Word) :
    (∑ y, variant adjoint fourier y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  calc
    _ ≤ (46 / 4294967296 : ℝ) ^ 2 * (∑ y, variant adjoint fourier y x ^ 2) :=
      fourth_le_square _ (fun y => (variant_entry_lt adjoint fourier x y).le)
    _ < (46 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) :=
      mul_lt_mul_of_pos_left (PaperAESSource.residualVariant_column_energy_lt_current adjoint fourier x) (by norm_num)
    _ < _ := by norm_num

-- Route dependency: the trace premise uses the owned physical degree-HS assembly.
theorem variant_total_fourth_lt (adjoint fourier : Bool) :
    (∑ y, ∑ x, variant adjoint fourier y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) := by
  calc
    _ ≤ ∑ y, (46 / 4294967296 : ℝ) ^ 2 *
        (∑ x, variant adjoint fourier y x ^ 2) := by
      apply Finset.sum_le_sum
      intro y _
      exact fourth_le_square _ (fun x => (variant_entry_lt adjoint fourier x y).le)
    _ = (46 / 4294967296 : ℝ) ^ 2 *
        (∑ y, ∑ x, variant adjoint fourier y x ^ 2) := (Finset.mul_sum _ _ _).symm
    _ < (46 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) :=
      mul_lt_mul_of_pos_left (PaperWordTraceVariants.variant_trace_lt adjoint fourier) (by norm_num)
    _ < _ := by norm_num

theorem mixed_row_fourth_lt (adjoint eL eR : Bool) (y : AES.Word) :
    (∑ x, mixed adjoint eL eR y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  cases eL <;> cases eR
  · rw [mixed_same_flags]
    exact variant_row_fourth_lt adjoint false y
  · exact AES8.PaperExceptionalWordFourth.row_fourth_lt adjoint y
  · simp_rw [mixed_left_transpose]
    exact AES8.PaperExceptionalWordFourth.column_fourth_lt (!adjoint) y
  · rw [mixed_same_flags]
    exact variant_row_fourth_lt adjoint true y

theorem mixed_column_fourth_lt (adjoint eL eR : Bool) (x : AES.Word) :
    (∑ y, mixed adjoint eL eR y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  cases eL <;> cases eR
  · rw [mixed_same_flags]
    exact variant_column_fourth_lt adjoint false x
  · exact AES8.PaperExceptionalWordFourth.column_fourth_lt adjoint x
  · simp_rw [mixed_left_transpose]
    exact AES8.PaperExceptionalWordFourth.row_fourth_lt (!adjoint) x
  · rw [mixed_same_flags]
    exact variant_column_fourth_lt adjoint true x

theorem mixed_total_fourth_lt (adjoint eL eR : Bool) :
    (∑ y, ∑ x, mixed adjoint eL eR y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) := by
  cases eL <;> cases eR
  · rw [mixed_same_flags]
    exact variant_total_fourth_lt adjoint false
  · exact AES8.PaperExceptionalWordFourth.total_fourth_lt adjoint
  · simp_rw [mixed_left_transpose]
    rw [Finset.sum_comm]
    exact AES8.PaperExceptionalWordFourth.total_fourth_lt (!adjoint)
  · rw [mixed_same_flags]
    exact variant_total_fourth_lt adjoint true

end AES8.PaperExceptionalWordVariants
