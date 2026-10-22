import AES8.Math.WordActivityFrame
import AES8.Math.PaperFiberKernel
import AESConcrete.ActivityMinorContraction
import AESConcrete.WordChannelCommutation

/-!
# Literal residual/frame analysis of a pointed tensor channel

The retained coordinate map is a residual projection. Each omitted leg is
one actual normalized zero/full-uniform frame column. Its transpose is the
input synthesis map, with counting-measure adjoint and no scalar factor.
Constructive identities only; no attacks, searches or numerical assumptions.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityMinorTransport
open AESMixing WordActivityFrame
open AESConcrete.ActivityMinorContraction
open PaperKernelBounds PaperFiberKernel
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- A genuine one-sided frame contraction, retaining physical positions. -/
def analysis (S : Finset J) (u : J → Bool)
    (y : S → V) (x : J → V) : ℝ :=
  ∏ j : J, if h : j ∈ S then residualProjection 0 (y ⟨j,h⟩) (x j)
    else wordFrame 0 (u j) (x j)

def synthesis (S : Finset J) (u : J → Bool)
    (x : J → V) (y : S → V) : ℝ := analysis S u y x

theorem analysis_product (S : Finset J) (u : J → Bool)
    (y : S → V) (x : J → V) :
    analysis S u y x = ∏ j : J,
      if h : j ∈ S then residualProjection 0 (y ⟨j,h⟩) (x j)
      else wordFrame 0 (u j) (x j) := by rfl

theorem residual_left {D : V → V → ℝ}
    (hD : PointedBistochastic D 0) :
    kernelCompose (residualProjection (0 : V)) D = residualMatrix D 0 := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, residualProjection_action, wordResidual,
    hD.average_action]
  change action D f - wordAverage 0 f = action (D - activityMatrix 0) f
  rw [kernel_action_sub, activityMatrix_action]

theorem frame_left {D : V → V → ℝ}
    (hD : PointedBistochastic D 0) (b : Bool) (x : V) :
    (∑ y : V, wordFrame 0 b y * D y x) = wordFrame 0 b x := by
  cases b
  · simp only [wordFrame, Bool.false_eq_true, if_false, identityKernel,
      ite_mul, one_mul, zero_mul]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using hD.zero_row x
  · simp only [wordFrame, if_true, ← Finset.mul_sum, hD.column_sum, mul_one]

/-- Each retained leg becomes the actual residual; each omitted leg is fixed.
This identity has no assumption on the number of retained coordinates. -/
theorem analysis_channel (S : Finset J) (u : J → Bool)
    (D : J → V → V → ℝ) (hD : ∀ j, PointedBistochastic (D j) 0)
    (y : S → V) (x : J → V) :
    kernelCompose (analysis S u) (coordinateKernel D) y x =
      ∏ j : J, if h : j ∈ S then residualMatrix (D j) 0 (y ⟨j,h⟩) (x j)
        else wordFrame 0 (u j) (x j) := by
  unfold kernelCompose
  simp_rw [analysis_product]
  simp only [coordinateKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : J) (v : V) =>
    (if h : j ∈ S then residualProjection 0 (y ⟨j,h⟩) v
      else wordFrame 0 (u j) v) * D j v (x j))]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · simp only [dif_pos hj]
    exact congrFun (congrFun (residual_left (hD j)) (y ⟨j,hj⟩)) (x j)
  · simp only [dif_neg hj]
    exact frame_left (hD j) (u j) (x j)

/-- The two genuine adjoints are analysis and synthesis, with no q factor. -/
theorem analysis_adjoint (S : Finset J) (u : J → Bool) :
    (kernelOperator (analysis (V := V) S u)).adjoint =
      kernelOperator (synthesis S u) := by
  rw [kernelOperator_adjoint]
  rfl

theorem synthesis_adjoint (S : Finset J) (u : J → Bool) :
    (kernelOperator (synthesis (V := V) S u)).adjoint =
      kernelOperator (analysis S u) := by
  rw [kernelOperator_adjoint]
  rfl

end AES8.PaperActivityMinorTransport
