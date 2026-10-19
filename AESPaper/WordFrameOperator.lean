import AESPaper.WordFrameCoordinates
import AESPaper.RectangularBounds

/-!
# Canonical activity-frame kernels and their signed operator bounds

The canonical kernel is G^-1 V*, rather than frame analysis V* alone.
Its bound follows from the actual orthogonal activity projector and the
proved inverse-Gram conditioning. Its transpose has the same bound. Both
identities with the activity projector are exact and include empty activity
coordinate types. No sign, mass, or product-input assumption is imposed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordFrameOperator
open AESMixing
open AESPaper.WordActivityFrame
open AESPaper.WordFrameCoordinates
open AESPaper.RectangularFourier (rectAction EnergyBound)

variable {I : Type*} [Fintype I] [DecidableEq I]

def analysisKernel (s : I → Bool) (x : I → AES.Word) : ℝ := frameColumn s x
def synthesisKernel (x : I → AES.Word) (s : I → Bool) : ℝ := frameColumn s x

/-- Actual canonical coordinates, with the inverse Gram retained. -/
def canonicalKernel : (I → Bool) → (I → AES.Word) → ℝ :=
  kernelCompose frameInverse analysisKernel

theorem tensorActivityKernel_symmetric (x y : I → AES.Word) :
    tensorActivityKernel x y = tensorActivityKernel y x := by
  unfold tensorActivityKernel
  apply Finset.prod_congr rfl
  intro i _
  exact activityMatrix_symmetric 0 (x i) (y i)

/-- The actual activity projection is self-adjoint in counting measure. -/
theorem projectActivity_inner (f g : (I → AES.Word) → ℝ) :
    (∑ x, projectActivity f x * g x) = ∑ x, f x * projectActivity g x := by
  have hs : RectangularBounds.transpose (tensorActivityKernel (I := I)) =
      tensorActivityKernel := by
    funext x y
    exact tensorActivityKernel_symmetric y x
  have h := RectangularBounds.transpose_inner (tensorActivityKernel (I := I)) f g
  rw [hs] at h
  exact h

/-- Symmetry and the proved idempotence make the actual tensor activity
projector a contraction, on every signed input. -/
theorem projectActivity_energy_le (f : (I → AES.Word) → ℝ) :
    (∑ x, projectActivity f x ^ 2) ≤ ∑ x, f x ^ 2 := by
  have hp := projectActivity_inner f (projectActivity f)
  rw [projectActivity_idempotent] at hp
  have he : (∑ x, projectActivity f x ^ 2) =
      ∑ x, projectActivity f x * f x := by
    simpa only [pow_two, mul_comm] using hp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (projectActivity f) f
  rw [← he] at hc
  have hn : 0 ≤ ∑ x, projectActivity f x ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : (∑ x, projectActivity f x ^ 2) = 0
  · rw [hz]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hpos : 0 < ∑ x, projectActivity f x ^ 2 := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

theorem canonicalKernel_action (f : (I → AES.Word) → ℝ) :
    rectAction canonicalKernel f = coefficients f := by
  change action (kernelCompose frameInverse analysisKernel) f = coefficients f
  rw [kernelCompose_action]
  rfl

/-- The inverse-frame coefficient map costs exactly one conditioning factor. -/
theorem canonicalKernel_energyBound :
    EnergyBound (canonicalKernel (I := I)) (conditioningFactor (Fintype.card I)) := by
  intro f
  rw [canonicalKernel_action, conditioningFactor_sq]
  exact (coefficients_energy_projection f).trans
    (mul_le_mul_of_nonneg_left (projectActivity_energy_le f) (by positivity))

theorem canonicalTranspose_energyBound :
    EnergyBound (RectangularBounds.transpose (canonicalKernel (I := I)))
      (conditioningFactor (Fintype.card I)) :=
  RectangularBounds.energyBound_transpose _ _ canonicalKernel_energyBound

/-- Symmetry of the exact inverse Gram identifies the dual synthesis map. -/
theorem canonicalTranspose_eq :
    RectangularBounds.transpose (canonicalKernel (I := I)) =
      kernelCompose synthesisKernel frameInverse := by
  funext x s
  unfold RectangularBounds.transpose canonicalKernel kernelCompose analysisKernel synthesisKernel
  apply Finset.sum_congr rfl
  intro t _
  rw [frameInverse_symmetric s t]
  ring

theorem canonicalTranspose_action (f : (I → Bool) → ℝ) :
    rectAction (RectangularBounds.transpose (canonicalKernel (I := I))) f =
      synthesize (action frameInverse f) := by
  rw [canonicalTranspose_eq]
  change action (kernelCompose synthesisKernel frameInverse) f = _
  rw [kernelCompose_action]
  rfl

/-- S C is the actual orthogonal activity projection. -/
theorem synthesis_canonical_eq_project :
    kernelCompose (synthesisKernel (I := I)) canonicalKernel = tensorActivityKernel :=
  tensorActivityKernel_factorization.symm

/-- C* A is the same actual orthogonal activity projection. This is the
second frame factor used after analysis contractions, not an extra inverse
applied to those contractions. -/
theorem canonicalTranspose_analysis_eq_project :
    kernelCompose (RectangularBounds.transpose (canonicalKernel (I := I))) analysisKernel =
      tensorActivityKernel := by
  classical
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  change rectAction (RectangularBounds.transpose canonicalKernel) (analyze f) =
    projectActivity f
  rw [canonicalTranspose_action]
  exact synthesize_coefficients f

/-- A finite untouched family remains arbitrary and jointly signed. -/
theorem projectActivity_weighted_sum {B : Type*} [Fintype B]
    (f : B → (I → AES.Word) → ℝ) (c : B → ℝ) :
    projectActivity (fun x => ∑ b : B, f b x * c b) =
      fun x => ∑ b : B, projectActivity (f b) x * c b := by
  funext x
  unfold projectActivity action
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end AESPaper.WordFrameOperator
