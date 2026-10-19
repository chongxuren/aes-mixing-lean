import AESPaper.ActivityKernel
import AESPaper.ActivityEnergy
import AESPaper.WordDamping

/-!
# Actual centered word-activity bound

The MDS count kernel, its orthonormal indicator representation and the exact
matrix certificate are composed here on the physical word boundary. Centering
is essential: without it the two stationary directions have norm one.
This supplies the activity block only, not the full H Pi H Pi comparison.
-/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace AESPaper.ActivityBound
open AESMixing AESConcrete
open AESPaper.ProfileSpace AESPaper.GroupedRecurrence

/-- Exact conversion of the source-count coefficients to the checked matrix. -/
theorem aesKernel_lifted : ActivityKernel.aesKernel =
    ActivityEnergy.liftedKernel (ActivityKernel.normalizedIndicator (V := AES.Word))
      ActivityMatrix.matrix := by
  funext y x
  rw [ActivityKernel.aesKernel_normalized_formula]
  unfold ActivityEnergy.liftedKernel
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [ActivityMatrix.matrix, ActivityMatrix.coefficient, ActivityMatrix.mass,
    ActivityMatrix.q, ActivityKernel.activityCoefficient, ActivityKernel.activityMass,
    Fin.val_succ, show a.val+1+(b.val+1) = a.val+b.val+2 by omega]

theorem aesKernel_energy (f : AES.WordState → ℝ) :
    (∑ y, action ActivityKernel.aesKernel f y^2) ≤
      ((601/100)/ActivityMatrix.q^2)^2 * ∑ x, f x^2 := by
  rw [aesKernel_lifted]
  exact ActivityEnergy.activity_lifted_energy _
    (ActivityKernel.normalizedIndicator_gram word_card_gt_one) f

def activityBoundary (f : ProfileSpace.State) : ProfileSpace.State :=
  component 0 (WithLp.toLp 2 (Pi (fun x => component 0 f x)))

theorem projected_input (f : ProfileSpace.State) :
    degreeComponent (0 : AES.Word) 0 (fun x => component 0 f x) =
      (fun x => component 0 f x) := by
  have h := component_idempotent 0 f
  exact (funext (fun x => component_apply 0 (component 0 f) x)).symm.trans
    (congrArg (fun g : ProfileSpace.State => fun x => g x) h)

theorem activityBoundary_action (f : ProfileSpace.State) (hf : Centered f) :
    (fun x => activityBoundary f x) =
      action ActivityKernel.aesKernel (fun x => component 0 f x) := by
  rw [ActivityKernel.aesKernel_action (component 0 f) (component_centered 0 f hf),
    projected_input]
  exact funext (fun x => AESPaper.BoundaryZeros.component_toLp_apply 0
    (Pi (fun y => component 0 f y)) x)

/-- Actual activity-to-activity norm bound, with the input projection retained. -/
theorem activityBoundary_norm (f : ProfileSpace.State) (hf : Centered f) :
    ‖activityBoundary f‖ ≤ ((601/100)/ActivityMatrix.q^2) * ‖component 0 f‖ := by
  have h := l2_le_of_energy _ _ ((601/100)/ActivityMatrix.q^2) (by positivity)
    (aesKernel_energy (fun x => component 0 f x))
  rw [← activityBoundary_action f hf, l2_eq_norm, l2_eq_norm] at h
  exact h

/-- The same coefficient in the paper's q²=2^64 normalization. -/
theorem activityBoundary_norm_pow (f : ProfileSpace.State) (hf : Centered f) :
    ‖activityBoundary f‖ ≤ ((601/100)/(2:ℝ)^64) * ‖component 0 f‖ := by
  have hq : ActivityMatrix.q^2 = (2:ℝ)^64 := by norm_num [ActivityMatrix.q]
  simpa only [hq] using activityBoundary_norm f hf

/-- The paper's P0 H Pi H P0 block, using the checked word-layer operator. -/
def activitySandwich (f : ProfileSpace.State) : ProfileSpace.State :=
  component 0 (WordDamping.layer (WithLp.toLp 2
    (Pi (fun x => WordDamping.layer (component 0 f) x))))

theorem activitySandwich_eq (f : ProfileSpace.State) :
    activitySandwich f = activityBoundary f := by
  unfold activitySandwich
  rw [WordDamping.activity_layer, WordDamping.layer_activity]
  rfl

/-- The activity constant supplying a=6.01 in the paper's block assembly. -/
theorem activitySandwich_norm (f : ProfileSpace.State) (hf : Centered f) :
    ‖activitySandwich f‖ ≤ ((601/100)/(2:ℝ)^64) * ‖component 0 f‖ := by
  rw [activitySandwich_eq]
  exact activityBoundary_norm_pow f hf

end AESPaper.ActivityBound
