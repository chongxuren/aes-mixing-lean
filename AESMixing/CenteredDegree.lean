import AESMixing.CenteredActivityGram

/-! On a centered whole-word input, the degree-zero diffusion response is
already centered. This permits use of the corrected Gram certificate in
the actual five-block norm argument. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem wordResidual_eq_self {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (f : V → ℝ) (hz : f z = 0) (hs : (∑ x, f x) = 0) :
    wordResidual z f = f := by
  funext x
  simp [wordResidual, wordAverage, nonzeroMean, hz, hs]

theorem degree_zero_diffusion_centered {V : Type*}
    [Fintype V] [Zero V] [DecidableEq V] (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (hL : L 0 = 0)
    (f : (Fin 4 → V) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    wordResidual 0 (degreeComponent 0 0 (fun x => degreeComponent 0 0 f (L.symm x))) =
      degreeComponent 0 0 (fun x => degreeComponent 0 0 f (L.symm x)) := by
  have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
    degree_zero_pointed (0 : V) hn
  have hLi : L.symm 0 = 0 := by
    apply L.injective
    simp [hL]
  apply wordResidual_eq_self
  · rw [← degreeKernel_action, hp.action_zero, hLi,
      ← degreeKernel_action, hp.action_zero]
    exact hz
  · rw [← degreeKernel_action, hp.action_sum, L.symm.sum_comp,
      ← degreeKernel_action, hp.action_sum]
    exact hs

end AESMixing
