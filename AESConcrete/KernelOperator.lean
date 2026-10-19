import AESConcrete.WordNormClosure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Counting-measure energy estimates as actual continuous-linear-map norms.
The finite kernel is unchanged; the Euclidean-space wrapper supplies the norm
used by the operator interfaces. No enumeration of the word space is performed.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete
open AESMixing

def kernelOperator {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  (Matrix.toEuclideanLin D).toContinuousLinearMap

theorem kernelOperator_apply {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) (f : EuclideanSpace ℝ V) (x : V) :
    kernelOperator D f x = action D (fun y => f y) x := by
  rfl

theorem kernelOperator_norm_le {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ f : V → ℝ, (∑ x, action D f x ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2) :
    ‖kernelOperator D‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply]
    using henergy (fun x => f x)

def wordResidualOperator :
    EuclideanSpace ℝ AES.Word →L[ℝ] EuclideanSpace ℝ AES.Word :=
  kernelOperator (residualMatrix AES.wordSuperboxKernel 0)

/-- Concrete intermediate bound. The sharper fixed-certificate constant is a
separate theorem; this older constant does not discharge that obligation. -/
theorem wordResidualOperator_norm_le_eleven :
    ‖wordResidualOperator‖ ≤ (11 : ℝ) / 65536 := by
  exact kernelOperator_norm_le _ (by norm_num) WordNorm.word_superbox_residual_energy

end AESConcrete
