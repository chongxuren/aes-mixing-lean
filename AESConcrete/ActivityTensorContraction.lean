import AESConcrete.ActivityFrameContraction
import AESMixing.CoordinateTensor

/-!
# Exact activity contraction on arbitrary coordinate sets

The normalized byte frame is not orthogonal. This module tensors its actual
dual-frame identities and retains the inverse metric in every inner product.
There is no energy estimate or independence hypothesis. Constructive scope
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityTensorContraction
open AESMixing AESConcrete.ActivityFrame AESConcrete.ActivityFrameContraction

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Zero V] [DecidableEq V]

def tensorDual (s : I → Bool) (x : I → V) : ℝ :=
  ∏ i, dualFrame (s i) (x i)

def tensorContraction (f : (I → V) → ℝ) (s : I → Bool) : ℝ :=
  ∑ x, frameColumn s x * f x

theorem activity_dual_projection (hV : Fintype.card V = 256) (x y : V) :
    activityMatrix 0 x y = ∑ s : Bool, dualFrame s x * byteFrame s y := by
  rw [byte_projection hV, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [dualFrame, Finset.sum_mul]

theorem tensor_projection (hV : Fintype.card V = 256) (x y : I → V) :
    coordinateKernel (fun _ : I => activityMatrix (0 : V)) x y =
      ∑ s : I → Bool, tensorDual s x * frameColumn s y := by
  unfold coordinateKernel
  simp_rw [activity_dual_projection hV]
  rw [Fintype.prod_sum]
  simp only [tensorDual, frameColumn, Finset.prod_mul_distrib]

theorem tensorDual_gram (hV : Fintype.card V = 256) (s t : I → Bool) :
    (∑ x : I → V, tensorDual s x * tensorDual t x) = frameInverse s t := by
  unfold tensorDual frameInverse
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => dualFrame (s i) x * dualFrame (t i) x)]
  simp_rw [dualFrame_gram hV]

theorem projected_response (hV : Fintype.card V = 256)
    (f : (I → V) → ℝ) (x : I → V) :
    action (coordinateKernel (fun _ : I => activityMatrix (0 : V))) f x =
      ∑ s : I → Bool, tensorDual s x * tensorContraction f s := by
  unfold action
  simp_rw [tensor_projection hV, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [tensorContraction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem projected_inner (hV : Fintype.card V = 256)
    (f g : (I → V) → ℝ) :
    (∑ x : I → V,
      action (coordinateKernel (fun _ : I => activityMatrix (0 : V))) f x *
      action (coordinateKernel (fun _ : I => activityMatrix (0 : V))) g x) =
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameInverse s t * tensorContraction f s * tensorContraction g t := by
  simp_rw [projected_response hV]
  change (∑ x : I → V,
    action (fun x s => tensorDual s x) (tensorContraction f) x *
    action (fun x s => tensorDual s x) (tensorContraction g) x) = _
  rw [kernel_bilinear]
  simp_rw [tensorDual_gram hV]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Exact inverse-metric identity on the actual tensor activity range. -/
theorem fixed_inner (hV : Fintype.card V = 256)
    (f g : (I → V) → ℝ)
    (hf : action (coordinateKernel (fun _ : I => activityMatrix (0 : V))) f = f)
    (hg : action (coordinateKernel (fun _ : I => activityMatrix (0 : V))) g = g) :
    (∑ x : I → V, f x * g x) =
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameInverse s t * tensorContraction f s * tensorContraction g t := by
  simpa only [hf, hg] using projected_inner hV f g

/-- Marked outputs may be correlated; only the activity legs are contracted. -/
theorem fixed_family_inner {Y : Type*} [Fintype Y]
    (hV : Fintype.card V = 256) (f g : Y → (I → V) → ℝ)
    (hf : ∀ y, action (coordinateKernel (fun _ : I => activityMatrix (0 : V)))
      (f y) = f y)
    (hg : ∀ y, action (coordinateKernel (fun _ : I => activityMatrix (0 : V)))
      (g y) = g y) :
    (∑ y : Y, ∑ x : I → V, f y x * g y x) =
      ∑ s : I → Bool, ∑ t : I → Bool, frameInverse s t *
        ∑ y : Y, tensorContraction (f y) s * tensorContraction (g y) t := by
  simp_rw [fixed_inner hV _ _ (hf _) (hg _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.mul_sum, mul_assoc]

end AESConcrete.ActivityTensorContraction
