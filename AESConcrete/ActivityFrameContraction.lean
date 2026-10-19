import AESConcrete.ActivityFrame

/-!
# Contraction of the remaining output activity coordinate

The contracted vectors use inner products with the normalized frame. Their
Gram must be weighted by the inverse frame metric. This module proves that
identity for the actual activity projection, before any MDS case estimates.
Constructive mathematics only; no attacks or manuscript changes.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityFrameContraction
open AESMixing AESConcrete.ActivityFrame
variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

def contraction (f : V → ℝ) (s : Bool) : ℝ := ∑ x, byteFrame s x * f x

def dualFrame (s : Bool) (x : V) : ℝ := ∑ t : Bool, byteFrame t x * byteInverse t s

theorem projected_response (hV : Fintype.card V = 256) (f : V → ℝ) (x : V) :
    action (activityMatrix 0) f x = ∑ s : Bool, dualFrame s x * contraction f s := by
  unfold action
  simp_rw [byte_projection hV, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ s : Bool, ∑ y : V, ∑ t : Bool,
      (byteFrame s x * byteInverse s t * byteFrame t y) * f y) =
      ∑ s : Bool, ∑ t : Bool,
        byteFrame s x * byteInverse s t * contraction f t := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t _
          simp only [contraction, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [dualFrame, Finset.sum_mul]

theorem dualFrame_gram (hV : Fintype.card V = 256) (s t : Bool) :
    (∑ x : V, dualFrame s x * dualFrame t x) = byteInverse s t := by
  change (∑ x : V,
    action (fun x s => byteFrame s x) (fun u => byteInverse u s) x *
    action (fun x s => byteFrame s x) (fun u => byteInverse u t) x) = _
  rw [kernel_bilinear]
  simp_rw [byte_gram hV]
  cases s <;> cases t <;> norm_num [byteInverse, byteMetric]

/-- Exact inverse-metric identity for the remaining activity coordinate. -/
theorem projected_inner (hV : Fintype.card V = 256) (f g : V → ℝ) :
    (∑ x : V, action (activityMatrix 0) f x * action (activityMatrix 0) g x) =
      ∑ s : Bool, ∑ t : Bool, byteInverse s t * contraction f s * contraction g t := by
  simp_rw [projected_response hV]
  change (∑ x : V,
    action (fun x s => dualFrame s x) (contraction f) x *
    action (fun x s => dualFrame s x) (contraction g) x) = _
  rw [kernel_bilinear]
  simp_rw [dualFrame_gram hV]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The identity remains exact for arbitrary correlated marked outputs. -/
theorem projected_tensor_inner {Y : Type*} [Fintype Y]
    (hV : Fintype.card V = 256) (f g : Y → V → ℝ) :
    (∑ y : Y, ∑ x : V,
      action (activityMatrix 0) (f y) x * action (activityMatrix 0) (g y) x) =
      ∑ s : Bool, ∑ t : Bool, byteInverse s t *
        ∑ y : Y, contraction (f y) s * contraction (g y) t := by
  simp_rw [projected_inner hV]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.mul_sum, mul_assoc]

end AESConcrete.ActivityFrameContraction
