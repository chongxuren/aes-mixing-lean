import AESMixing.DegreeCentering
import AESMixing.L2Sums

/-! A five-by-five scalar comparison controls the original operator on
the orthogonal byte-degree decomposition. This is the explicit finite
coordinate version of the block-norm argument in the paper. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem action_sum_family {I V W : Type*} [Fintype I] [Fintype V]
    (K : W → V → ℝ) (f : I → V → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem action_degree_decomposition {V W : Type*} [Fintype V] [DecidableEq V]
    (z : V) (K : W → (Fin 4 → V) → ℝ) (f : (Fin 4 → V) → ℝ) :
    action K f = fun y => ∑ j, action K (degreeComponent z j f) y := by
  have h := congrArg (action K) (degreeComponent_decomposition z f)
  rw [action_sum_family] at h
  exact h.symm

theorem degree_action_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (i : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z i (action K f) =
      fun y => ∑ j, degreeComponent z i (action K (degreeComponent z j f)) y := by
  rw [← degreeKernel_action,action_degree_decomposition z K f,action_sum_family]
  simp only [degreeKernel_action]

theorem degree_matrix_energy {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (B : Fin 5 → Fin 5 → ℝ)
    (c : ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (henergy : ∀ v : Fin 5 → ℝ, (∑ i, action B v i^2) ≤ c^2*∑ j, v j^2)
    (f : (Fin 4 → V) → ℝ)
    (hblock : ∀ i j, l2 (degreeComponent z i (action K (degreeComponent z j f))) ≤
      B i j*l2 (degreeComponent z j f)) :
    (∑ x, action K f x^2) ≤ c^2*∑ x, f x^2 := by
  have hi (i : Fin 5) : l2 (degreeComponent z i (action K f)) ≤
      action B (fun j => l2 (degreeComponent z j f)) i := by
    rw [degree_action_decomposition z K i f]
    exact (l2_finset_sum_le Finset.univ
      (fun j => degreeComponent z i (action K (degreeComponent z j f)))).trans
      (Finset.sum_le_sum (fun j _ => hblock i j))
  have hs (i : Fin 5) : (∑ x, degreeComponent z i (action K f) x^2) ≤
      action B (fun j => l2 (degreeComponent z j f)) i^2 := by
    have hp : 0 ≤ action B (fun j => l2 (degreeComponent z j f)) i :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (l2_nonneg _))
    simpa only [l2_sq] using (sq_le_sq₀ (l2_nonneg _) hp).mpr (hi i)
  calc
    _ = ∑ i, ∑ x, degreeComponent z i (action K f) x^2 :=
      (degreeComponent_pythagoras z hn (action K f)).symm
    _ ≤ ∑ i, action B (fun j => l2 (degreeComponent z j f)) i^2 :=
      Finset.sum_le_sum (fun i _ => hs i)
    _ ≤ c^2*∑ j, l2 (degreeComponent z j f)^2 := henergy _
    _ = _ := by simp only [l2_sq,degreeComponent_pythagoras z hn f]

end AESMixing
