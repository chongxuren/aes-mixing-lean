import AES8.Math.PaperActivityArrayFrame
import AES8.Math.PaperActivityArrayBlocks

/-!
# Actual canonical coordinates and projection laws

Candidate source; diagnostic and review status is recorded in adjacent receipts. The inverse-frame map is `G⁻¹ Φ*`. Its energy bound
uses sharp conditioning of the actual synthesis and contraction of the
actual activity projection. Both reconstruction orientations are proved.
No support, projector law or conditioning estimate is assumed here.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators

namespace AES8.PaperActivityArrayCoordinates
open AESMixing WordActivityFrame PaperActivityArrayFrame PaperActivityArrayBlocks

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def analysisKernel (z : V) (s : I → Bool) (x : I → V) : ℝ := frameColumn z s x
def synthesisKernel (z : V) (x : I → V) (s : I → Bool) : ℝ := frameColumn z s x
def canonicalKernel (z : V) : (I → Bool) → (I → V) → ℝ :=
  kernelCompose (frameInverse V) (analysisKernel z)
def tensorActivityKernel (z : V) (x y : I → V) : ℝ :=
  ∏ i, activityMatrix z (x i) (y i)
def projectActivity (z : V) (f : (I → V) → ℝ) : (I → V) → ℝ :=
  action (tensorActivityKernel z) f

theorem tensorActivityKernel_eq_productProjection (z : V) :
    tensorActivityKernel (I := I) z = productProjection z (fun _ => false) := by
  funext x y
  simp [tensorActivityKernel, productProjection, degreePiece]

theorem tensorActivityKernel_symmetric (z : V) (x y : I → V) :
    tensorActivityKernel z x y = tensorActivityKernel z y x := by
  unfold tensorActivityKernel
  apply Finset.prod_congr rfl
  intro i _
  exact activityMatrix_symmetric z (x i) (y i)

theorem tensorActivityKernel_idempotent (z : V) (hq : 1 < Fintype.card V) :
    kernelCompose (tensorActivityKernel (I := I) z) (tensorActivityKernel z) =
      tensorActivityKernel z := by
  rw [tensorActivityKernel_eq_productProjection, productProjection_compose z hq]
  simp

theorem projectActivity_idempotent (z : V) (hq : 1 < Fintype.card V)
    (f : (I → V) → ℝ) : projectActivity z (projectActivity z f) = projectActivity z f := by
  unfold projectActivity
  rw [← kernelCompose_action, tensorActivityKernel_idempotent z hq]

theorem projectActivity_inner (z : V) (f g : (I → V) → ℝ) :
    (∑ x, projectActivity z f x * g x) = ∑ x, f x * projectActivity z g x := by
  have hs : transpose (tensorActivityKernel (I := I) z) = tensorActivityKernel z := by
    funext x y
    exact tensorActivityKernel_symmetric z y x
  have h := transpose_inner (tensorActivityKernel z) f g
  rw [hs] at h
  exact h

/-- Orthogonal projection contraction on every signed physical vector. -/
theorem projectActivity_energy_le (z : V) (hq : 1 < Fintype.card V)
    (f : (I → V) → ℝ) :
    (∑ x, projectActivity z f x ^ 2) ≤ ∑ x, f x ^ 2 := by
  have hp := projectActivity_inner z f (projectActivity z f)
  rw [projectActivity_idempotent z hq] at hp
  have he : (∑ x, projectActivity z f x ^ 2) = ∑ x, projectActivity z f x * f x := by
    simpa only [pow_two, mul_comm] using hp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (projectActivity z f) f
  rw [← he] at hc
  have hn : 0 ≤ ∑ x, projectActivity z f x ^ 2 := by positivity
  by_cases hz : (∑ x, projectActivity z f x ^ 2) = 0
  · rw [hz]
    positivity
  · have hpos := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

/-- Exact synthesis--inverse--analysis factorization of the physical projector. -/
theorem synthesis_canonical_eq_project (z : V) (hq : 1 < Fintype.card V) :
    kernelCompose (synthesisKernel (I := I) z) (canonicalKernel z) =
      tensorActivityKernel z := by
  funext x y
  simpa only [synthesisKernel, canonicalKernel, analysisKernel, tensorActivityKernel,
    kernelCompose, Finset.mul_sum, mul_assoc] using (frame_projection z hq x y).symm

theorem synthesis_canonical_action (z : V) (hq : 1 < Fintype.card V)
    (f : (I → V) → ℝ) :
    action (synthesisKernel z) (action (canonicalKernel z) f) = projectActivity z f := by
  rw [← kernelCompose_action, synthesis_canonical_eq_project z hq]
  rfl

/-- Canonical coordinates cost one sharp inverse-frame factor. -/
theorem canonicalKernel_energyBound (z : V) (hq : 1 < Fintype.card V) :
    EnergyBound (canonicalKernel (I := I) z) (conditioningFactor V (Fintype.card I)) := by
  intro f
  rw [conditioningFactor_sq hq]
  have hf := frame_coefficient_energy z hq (action (canonicalKernel z) f)
  have he : synthesize z (action (canonicalKernel z) f) = projectActivity z f :=
    synthesis_canonical_action z hq f
  rw [he] at hf
  exact hf.trans (mul_le_mul_of_nonneg_left (projectActivity_energy_le z hq f)
    (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (xi_lt_one hq)).le) _))

theorem canonicalTranspose_energyBound (z : V) (hq : 1 < Fintype.card V) :
    EnergyBound (transpose (canonicalKernel (I := I) z))
      (conditioningFactor V (Fintype.card I)) :=
  energyBound_transpose _ _ (canonicalKernel_energyBound z hq)

theorem canonicalTranspose_eq (z : V) :
    transpose (canonicalKernel (I := I) z) =
      kernelCompose (synthesisKernel z) (frameInverse V) := by
  funext x s
  unfold transpose canonicalKernel kernelCompose analysisKernel synthesisKernel
  apply Finset.sum_congr rfl
  intro t _
  rw [frameInverse_symmetric (V := V) s t]
  ring

/-- The opposite reconstruction orientation supplies the output factor. -/
theorem canonicalTranspose_analysis_eq_project (z : V) (hq : 1 < Fintype.card V) :
    kernelCompose (transpose (canonicalKernel (I := I) z)) (analysisKernel z) =
      tensorActivityKernel z := by
  rw [canonicalTranspose_eq]
  funext x y
  unfold kernelCompose synthesisKernel analysisKernel tensorActivityKernel
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simpa only [mul_assoc] using (frame_projection z hq x y).symm

theorem projectActivity_weighted_sum {B : Type*} [Fintype B]
    (z : V) (f : B → (I → V) → ℝ) (c : B → ℝ) :
    projectActivity z (fun x => ∑ b, f b x * c b) =
      fun x => ∑ b, projectActivity z (f b) x * c b := by
  funext x
  unfold projectActivity action
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end AES8.PaperActivityArrayCoordinates
