import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Estimates.Word.PaperWordMixedGram
import AES8.Estimates.Word.SharpWordNorm
import AES8.Estimates.Word.PaperWordTwoSwapsVariants
import AES8.Estimates.Word.PaperWordTraceVariants

/-!
# Current local word interface and all one-sided orientations

This assembles `lem:resources` and `localres:mixed-energy` of frozen paper
f902bb94. Columns use the current source proof. Strict operator bounds retain
the checked rational margin before applying exact Fourier isometries.
The one-sided operator is literally B F for each of the four residual B.
No entry or fourth-moment bound is asserted. Constructive checking only.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESLocalResources
open AESMixing AESConcrete PaperWordMixedGram
open AESConcrete.WordFourierCore AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The local interface on each actual residual orientation. -/
theorem local_resources (adjoint fourier : Bool) :
    ‖kernelOperator (variant adjoint fourier)‖ < 52 / (5 * Real.sqrt ((2 : ℝ) ^ 32)) ∧
    (∀ x, (∑ y, variant adjoint fourier y x ^ 2) < (2 / (15 * 4294967296) : ℝ)) ∧
    (∑ x, ∑ z, (∑ y, variant adjoint fourier y x * variant adjoint fourier y z) ^ 2) <
      (300 / 4294967296 : ℝ) ^ 2 :=
  ⟨SharpWordNorm.variant_operator_norm_lt adjoint fourier,
    PaperAESSource.residualVariant_column_energy_lt_current adjoint fourier,
    PaperWordTwoSwapsVariants.variant_gram_moment_lt adjoint fourier⟩

theorem mixed_column_energy_lt (adjoint eL eR : Bool) (x : AES.Word) :
    (∑ y, mixed adjoint eL eR y x ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
  have he : gram (mixed adjoint eL eR) x x = gram (variant adjoint eR) x x := by
    cases eL <;> cases eR <;>
      simp only [mixed, variant, Bool.false_eq_true, if_false, if_true,
        wordConjugate, fourierConjugate, left_fourier_gram]
    all_goals change (gram (kernelCompose (baseResidual adjoint) wordFourier) x x =
      gram (kernelCompose wordFourier (kernelCompose (baseResidual adjoint) wordFourier)) x x)
    all_goals rw [left_fourier_gram]
  rw [← gram_diagonal, he, gram_diagonal]
  exact PaperAESSource.residualVariant_column_energy_lt_current adjoint eR x

/-- Retain the strict margin, which is stronger than the rounded resource. -/
theorem mixed_sharp_energy (adjoint eL eR : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (mixed adjoint eL eR) f y ^ 2) ≤
      SharpWordNorm.rho ^ 2 * ∑ x, f x ^ 2 := by
  have hbase (g : AES.Word → ℝ) :
      (∑ y, action (baseResidual adjoint) g y ^ 2) ≤
        SharpWordNorm.rho ^ 2 * ∑ x, g x ^ 2 :=
    SharpWordNorm.variant_energy adjoint false g
  cases eL <;> cases eR
  · exact hbase f
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action]
    have h := hbase (action wordFourier f)
    rw [wordFourier_energy] at h
    exact h
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action,
      wordFourier_energy]
    exact hbase f
  · simp only [mixed, Bool.false_eq_true, if_false, if_true, kernelCompose_action,
      wordFourier_energy]
    have h := hbase (action wordFourier f)
    rw [wordFourier_energy] at h
    exact h

theorem mixed_operator_norm_lt (adjoint eL eR : Bool) :
    ‖kernelOperator (mixed adjoint eL eR)‖ < (52 / (5 * 65536) : ℝ) := by
  exact (kernelOperator_norm_le _ (by norm_num [SharpWordNorm.rho])
    (mixed_sharp_energy adjoint eL eR)).trans_lt (by norm_num [SharpWordNorm.rho])

-- Route dependency: the trace premise uses the owned physical degree-HS assembly.
theorem mixed_trace_lt (adjoint eL eR : Bool) :
    (∑ y, ∑ x, mixed adjoint eL eR y x ^ 2) < (4251 / 4294967296 : ℝ) := by
  have he (x : AES.Word) :
      (∑ y, mixed adjoint eL eR y x ^ 2) = ∑ y, variant adjoint eR y x ^ 2 := by
    rw [← gram_diagonal, ← gram_diagonal]
    cases eL <;> cases eR <;>
      simp only [mixed, variant, Bool.false_eq_true, if_false, if_true,
        wordConjugate, fourierConjugate, left_fourier_gram]
    all_goals change (gram (kernelCompose (baseResidual adjoint) wordFourier) x x =
      gram (kernelCompose wordFourier (kernelCompose (baseResidual adjoint) wordFourier)) x x)
    all_goals rw [left_fourier_gram]
  rw [Finset.sum_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  exact PaperWordTraceVariants.variant_trace_lt adjoint eR

/-- Literal one-sided transform of all four residual orientations. -/
def oneSided (adjoint fourier : Bool) : AES.Word → AES.Word → ℝ :=
  kernelCompose (variant adjoint fourier) wordFourier

theorem oneSided_eq_mixed (adjoint fourier : Bool) :
    oneSided adjoint fourier = mixed adjoint fourier (!fourier) := by
  cases fourier
  · rfl
  · apply kernel_action_ext
    intro f
    simp only [oneSided, variant, mixed, Bool.not_true, Bool.false_eq_true,
      if_false, if_true, kernelCompose_action, wordConjugate_action, wordFourier_twice]

theorem one_sided_resources (adjoint fourier : Bool) :
    ‖kernelOperator (oneSided adjoint fourier)‖ < (52 / (5 * 65536) : ℝ) ∧
    (∑ y, ∑ x, oneSided adjoint fourier y x ^ 2) < (4251 / 4294967296 : ℝ) ∧
    (∀ y, (∑ x, oneSided adjoint fourier y x ^ 2) < (2 / (15 * 4294967296) : ℝ)) ∧
    (∀ x, (∑ y, oneSided adjoint fourier y x ^ 2) < (2 / (15 * 4294967296) : ℝ)) := by
  rw [oneSided_eq_mixed]
  exact ⟨mixed_operator_norm_lt adjoint fourier (!fourier),
    mixed_trace_lt adjoint fourier (!fourier),
    PaperWordMixedGram.mixed_row_energy_lt adjoint fourier (!fourier),
    mixed_column_energy_lt adjoint fourier (!fourier)⟩
end AES8.PaperAESLocalResources
