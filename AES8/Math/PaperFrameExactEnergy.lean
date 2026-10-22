import AES8.Math.PaperActivityInputCoordinates

/-! Exact inverse-frame contraction of a physical energy. No row bound or
conditioning estimate is used in this identity. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFrameExactEnergy
open AESMixing WordActivityFrame PaperActivityInputCoordinates
set_option autoImplicit false
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

theorem inverse_symmetric (s t : I → Bool) : frameInverse V s t = frameInverse V t s := by
  unfold frameInverse wordInverse
  simp only [eq_comm]

theorem metric_symmetric (s t : I → Bool) : frameMetric V s t = frameMetric V t s := by
  unfold frameMetric wordMetric
  simp only [eq_comm]

theorem inverse_left (hq : 1 < Fintype.card V) (s t : I → Bool) :
    (∑ u : I → Bool, frameInverse V s u * frameMetric V u t) = if s = t then 1 else 0 := by
  calc
    _ = ∑ u : I → Bool, frameMetric V t u * frameInverse V u s := by
      apply Finset.sum_congr rfl
      intro u _
      rw [inverse_symmetric s u, metric_symmetric u t]
      ring
    _ = if t = s then 1 else 0 := frame_inverse hq t s
    _ = _ := by simp only [eq_comm]

def analysis (z : V) (g : (I → V) → ℝ) (s : I → Bool) : ℝ :=
  ∑ x, frameColumn z s x * g x

theorem analysis_synthesis (z : V) (hq : 1 < Fintype.card V)
    (c : (I → Bool) → ℝ) (t : I → Bool) :
    analysis z (fun x => ∑ u, frameColumn z u x * c u) t =
      ∑ u, frameMetric V t u * c u := by
  unfold analysis
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, frame_gram z hq]

theorem recover_coefficients (z : V) (hq : 1 < Fintype.card V)
    (c : (I → Bool) → ℝ) (s : I → Bool) :
    (∑ t : I → Bool, frameInverse V s t *
      analysis z (fun x => ∑ u, frameColumn z u x * c u) t) = c s := by
  simp_rw [analysis_synthesis z hq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, inverse_left hq]
  simp

theorem energy_eq_inverse_analysis (z : V) (hq : 1 < Fintype.card V)
    (g : (I → V) → ℝ) (c : (I → Bool) → ℝ)
    (hg : ∀ x, g x = ∑ s, frameColumn z s x * c s) :
    (∑ x : I → V, g x^2) = ∑ s : I → Bool, ∑ t : I → Bool,
      analysis z g s * analysis z g t * frameInverse V s t := by
  have hc (s : I → Bool) : c s = ∑ t, frameInverse V s t * analysis z g t := by
    rw [show g = (fun x => ∑ u, frameColumn z u x * c u) from funext hg]
    exact (recover_coefficients z hq c s).symm
  calc
    _ = ∑ x : I → V, g x * (∑ s, frameColumn z s x * c s) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← hg x]
      ring
    _ = ∑ s : I → Bool, analysis z g s * c s := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      unfold analysis
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp_rw [hc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- Literal projection energy retains the shared inverse metric in every
unmarked fiber; the original input may be an arbitrary joint function. -/
theorem projected_energy {J : Type*} [Fintype J] [DecidableEq J]
    (z : V) (hq : 1 < Fintype.card V) (S : Finset J) (f : (J → V) → ℝ) :
    let g := action (productProjection z (residualMask S)) f
    (∑ x : J → V, g x^2) = ∑ y : S → V,
      ∑ a : ↥(Sᶜ) → Bool, ∑ b : ↥(Sᶜ) → Bool,
        partialAnalysis z S g a y * partialAnalysis z S g b y * frameInverse V a b := by
  dsimp only
  rw [← (split S).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  exact energy_eq_inverse_analysis z hq _ (partialCoefficients z S f y)
    (projection_frame_range z hq S f y)

end AES8.PaperFrameExactEnergy
