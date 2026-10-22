import AES8.Reductions.Source.PaperAESSourceOrientations
/- Module role: Word-channel estimates and their normalization.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.WordFourierVariants
import AES8.Estimates.Word.PaperWordTraceVariants

/-!
# Actual one-sided word Fourier second moments

Right multiplication by the normalized word Fourier map preserves each row
energy. Left Fourier multiplication identifies each resulting column energy
with a simultaneous-Fourier variant. This supplies the genuine second-moment
and operator resources for R F and R^T F. It supplies no entry or fourth-moment
bound; the thin-code return route still requires those separate resources.

Constructive only; no attacks, proof bypasses or manuscript/predecessor edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.OneSidedWordEnergy
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.WordFourierCore
open AESConcrete.WordFourierVariants

def rightMixed (adjoint : Bool) : AES.Word → AES.Word → ℝ :=
  kernelCompose (baseResidual adjoint) wordFourier

theorem baseResidual_transpose (adjoint : Bool) (x y : AES.Word) :
    baseResidual (!adjoint) x y = baseResidual adjoint y x := by
  cases adjoint <;> rfl

/-- Row energy is exactly preserved, with the original output label retained. -/
theorem row_energy_eq (adjoint : Bool) (y : AES.Word) :
    (∑ x, rightMixed adjoint y x ^ 2) = ∑ x, baseResidual adjoint y x ^ 2 := by
  have he (x : AES.Word) : rightMixed adjoint y x =
      action wordFourier (fun z => baseResidual adjoint y z) x := by
    unfold rightMixed kernelCompose action
    apply Finset.sum_congr rfl
    intro z _
    rw [wordFourier_symmetric z x]
    ring
  simp_rw [he]
  exact wordFourier_energy _

/-- Column energy is exactly that of F R F, with the original input label retained. -/
theorem column_energy_eq (adjoint : Bool) (x : AES.Word) :
    (∑ y, rightMixed adjoint y x ^ 2) = ∑ y, variant adjoint true y x ^ 2 := by
  have he : action wordFourier (fun y => rightMixed adjoint y x) =
      fun y => variant adjoint true y x := by
    funext y
    rfl
  have hn := wordFourier_energy (fun y => rightMixed adjoint y x)
  rw [he] at hn
  exact hn.symm

theorem row_energy_lt (adjoint : Bool) (y : AES.Word) :
    (∑ x, rightMixed adjoint y x ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
  rw [row_energy_eq]
  calc
    _ = ∑ x, variant (!adjoint) false x y ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun z : ℝ => z ^ 2) (baseResidual_transpose adjoint x y).symm
    _ < _ := PaperAESSource.residualVariant_column_energy_lt_current (!adjoint) false y

theorem column_energy_lt (adjoint : Bool) (x : AES.Word) :
    (∑ y, rightMixed adjoint y x ^ 2) < (2 / (15 * 4294967296) : ℝ) := by
  rw [column_energy_eq]
  exact PaperAESSource.residualVariant_column_energy_lt_current adjoint true x

-- Route dependency: the trace premise uses the owned physical degree-HS assembly.
theorem trace_lt (adjoint : Bool) :
    (∑ y, ∑ x, rightMixed adjoint y x ^ 2) < (4251 / 4294967296 : ℝ) := by
  simp_rw [row_energy_eq]
  exact PaperWordTraceVariants.variant_trace_lt adjoint false

theorem energy_le (adjoint : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (rightMixed adjoint) f y ^ 2) ≤
      (21 / 131072 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  unfold rightMixed
  rw [kernelCompose_action, baseResidual_eq]
  have he := SharpDampedWordNorm.word_kernel_residual_energy
    (baseOrientation adjoint) (baseOrientation adjoint) adjoint
    (action wordFourier f)
  rw [wordFourier_energy] at he
  exact he

theorem operator_norm_le (adjoint : Bool) :
    ‖kernelOperator (rightMixed adjoint)‖ ≤ (21 / 131072 : ℝ) :=
  kernelOperator_norm_le _ (by norm_num) (energy_le adjoint)

end AES8.OneSidedWordEnergy
