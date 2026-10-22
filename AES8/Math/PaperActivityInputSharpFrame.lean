import AES8.Math.PaperActivityArrayFrame
import AES8.Math.PaperActivityInputCoordinates

/-! Sharp analysis on the tensor-frame range, and its application to the exact
residual-position coordinate splitting. This generic leaf imports the already
proved inverse-frame theorem; it has no AES response or scalar-rounding premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputSharpFrame
open AESMixing WordActivityFrame PaperActivityArrayFrame PaperActivityInputCoordinates
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def sharpLoss (V : Type*) [Fintype V] : ℝ := (1 - xi V)⁻¹

theorem sharpLoss_nonneg (hq : 1 < Fintype.card V) : 0 ≤ sharpLoss V :=
  inv_nonneg.mpr (sub_pos.mpr (xi_lt_one hq)).le

def analyze (z : V) (f : (I → V) → ℝ) (a : I → Bool) : ℝ :=
  ∑ x, frameColumn z a x * f x

/-- The exact dimension, rather than a uniform six-coordinate majorant. -/
theorem analysis_energy_lower (z : V) (hq : 1 < Fintype.card V)
    (c : (I → Bool) → ℝ) :
    (∑ x, synthesize z c x ^ 2) ≤
      sharpLoss V ^ Fintype.card I * ∑ a, analyze z (synthesize z c) a ^ 2 := by
  let e : ℝ := ∑ x, synthesize z c x ^ 2
  have he : 0 ≤ e := by positivity
  have hid : (∑ a, c a * analyze z (synthesize z c) a) = e := by
    unfold e analyze
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = (∑ a, frameColumn z a x * c a) * synthesize z c x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by change synthesize z c x * synthesize z c x = _; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (analyze z (synthesize z c))
  rw [hid] at hcs
  have hc := frame_coefficient_energy z hq c
  change (∑ a, c a ^ 2) ≤ sharpLoss V ^ Fintype.card I * e at hc
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ ∑ a, analyze z (synthesize z c) a ^ 2 by positivity)
  change e ≤ _
  by_cases hz : e = 0
  · rw [hz]
    exact mul_nonneg (pow_nonneg (sharpLoss_nonneg hq) _) (by positivity)
  · have hp : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    nlinarith

/-- Sharp output-analysis loss in precisely the unmarked coordinates.
The projected output can have arbitrary joint correlations. -/
theorem projected_energy_le_analysis {J : Type*} [Fintype J] [DecidableEq J]
    (z : V) (hq : 1 < Fintype.card V) (S : Finset J) (f : (J → V) → ℝ) :
    (∑ y, action (productProjection z (residualMask S)) f y ^ 2) ≤
      sharpLoss V ^ Fintype.card ↥(Sᶜ) *
        ∑ y : S → V, ∑ a : ↥(Sᶜ) → Bool,
          partialAnalysis z S (action (productProjection z (residualMask S)) f) a y ^ 2 := by
  let g := action (productProjection z (residualMask S)) f
  rw [← (split S).symm.sum_comp (fun y => g y ^ 2), Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have hr (u : ↥(Sᶜ) → V) : g ((split S).symm (y,u)) =
      synthesize z (partialCoefficients z S f y) u :=
    projection_frame_range z hq S f y u
  have h := analysis_energy_lower z hq (partialCoefficients z S f y)
  change (∑ u, g ((split S).symm (y,u)) ^ 2) ≤ _
  simp_rw [hr]
  change _ ≤ sharpLoss V ^ Fintype.card ↥(Sᶜ) *
    ∑ a, analyze z (fun u => g ((split S).symm (y,u))) a ^ 2
  simpa only [hr] using h

end AES8.PaperActivityInputSharpFrame
