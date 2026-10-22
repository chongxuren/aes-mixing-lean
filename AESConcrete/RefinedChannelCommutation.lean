import AESConcrete.DegreeResidualStep

/-!
# Pointed channels preserve exact support refinements

The three one-coordinate support projections commute with any pointed
bistochastic channel. Tensoring and summing gives commutation for the actual
refined projections. This algebraic interface permits diffusion and channel
damping to be composed on arbitrary joint real functions.

Constructive mathematics only. No experiment, return-cap or full AES theorem
is asserted here; the independent retained-key model is unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RefinedChannelCommutation
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.WordChannelCommutation
open AESConcrete.CenteredWordStepZeros (compose_sub_left compose_sub_right)

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pointed_zero_left {D : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) :
    kernelCompose (zeroMatrix z) D = zeroMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, zeroMatrix_action, zeroMatrix_action]
  funext y
  simp only [zeroPart, hD.action_zero]

theorem pointed_zero_right {D : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) :
    kernelCompose D (zeroMatrix z) = zeroMatrix z := by
  funext y x
  simp [kernelCompose, zeroMatrix, identityKernel, hD.zero_column]

theorem pointed_constant_left {D : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) :
    kernelCompose (constantMatrix z) D = constantMatrix z := by
  unfold constantMatrix
  rw [compose_sub_left, pointed_activity_left hD, pointed_zero_left hD]

theorem pointed_constant_right {D : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) :
    kernelCompose D (constantMatrix z) = constantMatrix z := by
  unfold constantMatrix
  rw [compose_sub_right, pointed_activity_right hD, pointed_zero_right hD]

theorem pointed_supportPiece_commutes {D : V → V → ℝ} {z : V}
    (hD : PointedBistochastic D z) (marked inactive : Bool) :
    kernelCompose (supportPiece z marked inactive) D =
      kernelCompose D (supportPiece z marked inactive) := by
  cases marked <;> cases inactive
  · change kernelCompose (constantMatrix z) D = kernelCompose D (constantMatrix z)
    rw [pointed_constant_left hD, pointed_constant_right hD]
  · change kernelCompose (zeroMatrix z) D = kernelCompose D (zeroMatrix z)
    rw [pointed_zero_left hD, pointed_zero_right hD]
  · exact (pointed_degreePiece_commutes hD true).symm
  · funext y x
    simp [supportPiece, kernelCompose]

theorem supportProduct_channel_commutes {I : Type*} [Fintype I] [DecidableEq I]
    (D : I → V → V → ℝ) (z : V) (hD : ∀ i, PointedBistochastic (D i) z)
    (marked inactive : I → Bool) :
    kernelCompose (supportProduct z marked inactive) (coordinateKernel D) =
      kernelCompose (coordinateKernel D) (supportProduct z marked inactive) := by
  change kernelCompose (coordinateKernel (fun i => supportPiece z (marked i) (inactive i)))
      (coordinateKernel D) =
    kernelCompose (coordinateKernel D)
      (coordinateKernel (fun i => supportPiece z (marked i) (inactive i)))
  rw [coordinateKernel_compose, coordinateKernel_compose]
  congr 1
  funext i
  exact pointed_supportPiece_commutes (hD i) (marked i) (inactive i)

theorem supportIndex_channel_commutes (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) {j : ℕ} (p : SupportIndex j) :
    kernelCompose (supportIndexKernel z p) (coordinateKernel (fun _ : Fin 4 => D)) =
      kernelCompose (coordinateKernel (fun _ : Fin 4 => D)) (supportIndexKernel z p) :=
  supportProduct_channel_commutes (fun _ => D) z (fun _ => hD) _ _

theorem refined_channel_commutes (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (d a : Fin 5) :
    kernelCompose (refinedKernel z d a) (coordinateKernel (fun _ : Fin 4 => D)) =
      kernelCompose (coordinateKernel (fun _ : Fin 4 => D)) (refinedKernel z d a) := by
  funext y x
  unfold refinedKernel kernelCompose
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact congrFun (congrFun (supportIndex_channel_commutes D z hD p) y) x
  · simp only [hp, if_false, zero_mul, mul_zero, Finset.sum_const_zero]

/-- The damping is charged to the refined input itself, with no pattern-count loss. -/
theorem refined_damped_energy (D : V → V → ℝ) (z : V)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D z) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D z) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2) (d a : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => D))
      (action (refinedKernel z d a) f) y ^ 2) ≤
      (ν ^ d.val) ^ 2 * ∑ x, action (refinedKernel z d a) f x ^ 2 := by
  have hfix : degreeComponent z d (action (refinedKernel z d a) f) =
      action (refinedKernel z d a) f := by
    rw [← degreeKernel_action, ← kernelCompose_action,
      degreeKernel_compose_refinedKernel z hn]
  have he := DegreeResidualStep.degree_input_energy D z hn hD ν hν d
    (action (refinedKernel z d a) f)
  rwa [hfix] at he

end AESConcrete.RefinedChannelCommutation
