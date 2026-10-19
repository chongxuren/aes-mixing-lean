import AESMixing.SuperboxStationarity
import AESMixing.ActivitySpan

/-! Exact word-channel commutation, separated from all quantitative bounds.
The alphabet in the generic lemmas is arbitrary. The concrete specialization
therefore concerns 32-bit words rather than byte-degree projections.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.WordChannelCommutation
open AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pointed_activity_left {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) :
    kernelCompose (activityMatrix z) D = activityMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action, h.average_action,
    activityMatrix_action]

theorem pointed_activity_right {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) :
    kernelCompose D (activityMatrix z) = activityMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action, h.action_average]

theorem pointed_degreePiece_commutes {D : V → V → ℝ} {z : V}
    (h : PointedBistochastic D z) (b : Bool) :
    kernelCompose D (degreePiece z b) = kernelCompose (degreePiece z b) D := by
  cases b
  · change kernelCompose D (activityMatrix z) = kernelCompose (activityMatrix z) D
    rw [pointed_activity_left h, pointed_activity_right h]
  · apply kernel_action_ext
    intro f
    change action (kernelCompose D (residualProjection z)) f =
      action (kernelCompose (residualProjection z) D) f
    rw [kernelCompose_action, kernelCompose_action,
      residualProjection_action, residualProjection_action]
    rw [wordResidual, wordResidual, action_sub, h.action_average, h.average_action]

theorem coordinate_pattern_commutes {I : Type*} [Fintype I] [DecidableEq I]
    {D : I → V → V → ℝ} {z : V}
    (h : ∀ i, PointedBistochastic (D i) z) (a : I → Bool) :
    kernelCompose (coordinateKernel D) (productProjection z a) =
      kernelCompose (productProjection z a) (coordinateKernel D) := by
  change kernelCompose (coordinateKernel D)
      (coordinateKernel (fun i => degreePiece z (a i))) =
    kernelCompose (coordinateKernel (fun i => degreePiece z (a i))) (coordinateKernel D)
  rw [coordinateKernel_compose, coordinateKernel_compose]
  congr 1
  funext i
  exact pointed_degreePiece_commutes (h i) (a i)

theorem coordinate_degree_commutes {D : Fin 4 → V → V → ℝ} {z : V}
    (h : ∀ i, PointedBistochastic (D i) z) (j : Fin 5)
    (f : (Fin 4 → V) → ℝ) :
    action (coordinateKernel D) (degreeComponent z j f) =
      degreeComponent z j (action (coordinateKernel D) f) := by
  have hp (a : Fin 4 → Bool) :
      action (coordinateKernel D) (action (productProjection z a) f) =
        action (productProjection z a) (action (coordinateKernel D) f) := by
    rw [← kernelCompose_action, ← kernelCompose_action, coordinate_pattern_commutes h]
  unfold degreeComponent
  rw [action_groupedFamily]
  simp_rw [hp]

theorem coordinate_degree_zero_left {D : Fin 4 → V → V → ℝ} {z : V}
    (h : ∀ i, PointedBistochastic (D i) z) :
    kernelCompose (degreeKernel z 0) (coordinateKernel D) = degreeKernel z 0 := by
  rw [degreeKernel_zero]
  change kernelCompose (coordinateKernel (fun _ : Fin 4 => activityMatrix z))
    (coordinateKernel D) = coordinateKernel (fun _ : Fin 4 => activityMatrix z)
  rw [coordinateKernel_compose]
  congr 1
  funext i
  exact pointed_activity_left (h i)

theorem parallel_word_degree_commutes (j : Fin 5) (f : AES.WordState → ℝ) :
    action AES.parallelSuperboxKernel (degreeComponent (0 : AES.Word) j f) =
      degreeComponent (0 : AES.Word) j (action AES.parallelSuperboxKernel f) :=
  coordinate_degree_commutes (fun _ => AES.word_superbox_pointed) j f

theorem parallel_word_activity_left (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 0 (action AES.parallelSuperboxKernel f) =
      degreeComponent (0 : AES.Word) 0 f := by
  change degreeComponent (0 : AES.Word) 0
    (action (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel)) f) = _
  rw [← degreeKernel_action, ← kernelCompose_action,
    coordinate_degree_zero_left (fun _ => AES.word_superbox_pointed), degreeKernel_action]

end AESConcrete.WordChannelCommutation
