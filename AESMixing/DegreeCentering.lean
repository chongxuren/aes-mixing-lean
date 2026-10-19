import AESMixing.ResidualCoordinates
import AESMixing.DegreeComposition

/-! Every byte-degree component of a centered whole-word vector remains
centered. This ensures the centered activity certificate is applicable
throughout the five-degree norm proof. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem productProjection_centered (z : V) (hn : 1 < Fintype.card V)
    (a : Fin 4 → Bool) (f : (Fin 4 → V) → ℝ)
    (hz : f (fun _ => z) = 0) (hs : (∑ x, f x) = 0) :
    action (productProjection z a) f (fun _ => z) = 0 ∧
      (∑ x, action (productProjection z a) f x) = 0 := by
  by_cases ha : a = fun _ => false
  · subst a
    have hp : PointedBistochastic (productProjection z (fun _ : Fin 4 => false))
        (fun _ => z) := coordinateKernel_pointed _ _ (fun _ => activityMatrix_pointed z hn)
    exact ⟨(hp.action_zero f).trans hz,(hp.action_sum f).trans hs⟩
  · have hk : ∃ k, a k = true := by
      by_contra h
      push Not at h
      exact ha (funext (fun k => Bool.eq_false_iff.mpr (h k)))
    obtain ⟨k,hk⟩ := hk
    exact ⟨productProjection_marked_zero z a k hk f _ rfl,
      productProjection_marked_sum z hn a k hk f⟩

theorem degreeComponent_centered (z : V) (hn : 1 < Fintype.card V)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ)
    (hz : f (fun _ => z) = 0) (hs : (∑ x, f x) = 0) :
    degreeComponent z j f (fun _ => z) = 0 ∧
      (∑ x, degreeComponent z j f x) = 0 := by
  unfold degreeComponent groupedFamily
  constructor
  · apply Finset.sum_eq_zero
    intro a _
    by_cases ha : degreeIndex a = j <;>
      simp [ha,(productProjection_centered z hn a f hz hs).1]
  · rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : degreeIndex a = j <;>
      simp [ha,(productProjection_centered z hn a f hz hs).2]

end AESMixing
