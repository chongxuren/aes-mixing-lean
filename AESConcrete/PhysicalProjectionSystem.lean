import AESConcrete.RefinedProjectionCompleteness
import AESRound.ProjectionAssembly

/-!
# Actual AES projected step and memory identities

All maps act on the same full counting-measure Euclidean state space.
The fourteen projections and the all-zero-state projection resolve the
identity. The omitted component is preserved by the centered step and
is invisible to all fourteen output types. The generic algebraic assembly
therefore applies without a change of ambient space.

This candidate supplies identities only. Physical norm caps, experiment
identification, initialization and total-variation conversion stay separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.PhysicalProjectionSystem
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (blockType physicalBlock)
open AESConcrete.RefinedProjectionCompleteness
open AESConcrete.CenteredWordStepZeros (centeredWordStepKernel)

section KernelAlgebra
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem operator_compose (A B : V → V → ℝ) :
    kernelOperator (kernelCompose A B) = (kernelOperator A).comp (kernelOperator B) := by
  ext f y
  change action (kernelCompose A B) (fun x => f x) y =
    action A (fun x => action B (fun z => f z) x) y
  rw [kernelCompose_action]

theorem operator_add (A B : V → V → ℝ) :
    kernelOperator (A+B) = kernelOperator A + kernelOperator B := by
  ext f y
  change action (A+B) (fun x => f x) y =
    action A (fun x => f x) y + action B (fun x => f x) y
  rw [kernel_action_add]
  rfl

theorem operator_sum {I : Type*} [Fintype I] (K : I → V → V → ℝ) :
    kernelOperator (fun y x => ∑ i, K i y x) = ∑ i, kernelOperator (K i) := by
  ext f y
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, kernelOperator_apply]
  change (∑ x, (∑ i, K i y x) * f x) = ∑ i, ∑ x, K i y x * f x
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem operator_identity :
    kernelOperator (identityKernel : V → V → ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext f y
  exact congrFun (identityKernel_action (fun x => f x)) y

theorem operator_zero : kernelOperator (0 : V → V → ℝ) = 0 := by
  ext f y
  simp [kernelOperator_apply, action]

end KernelAlgebra

abbrev State := EuclideanSpace ℝ AES.WordState

def projectionKernel (i : Fin 14) : AES.WordState → AES.WordState → ℝ :=
  refinedKernel (0 : AES.Word) (blockType i).1 (blockType i).2

/-- This is the concrete source-degree partition used by the low matrix. -/
def isLow (i : Fin 14) : Bool := decide ((blockType i).1.val ≤ 2)

def decomposition : AESRound.ProjectionAssembly.Decomposition (Fin 14) State where
  project := fun i => kernelOperator (projectionKernel i)
  update := kernelOperator centeredWordStepKernel
  remainder := kernelOperator (zeroMatrix (0 : AES.WordState))
  complete := by
    intro v
    have h := congrArg (fun K : AES.WordState → AES.WordState → ℝ => kernelOperator K)
      (fourteen_plus_zero (0 : AES.Word))
    have hz : AESConcrete.DegreeCentering.distinguishedState (0 : AES.Word) = (0 : AES.WordState) := rfl
    rw [operator_add, operator_sum, operator_identity, hz] at h
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.id_apply, projectionKernel] using congrArg (fun L => L v) h
  project_idempotent := by
    intro i v
    have h := congrArg (fun K : AES.WordState → AES.WordState → ℝ => kernelOperator K)
      (refined_compose (0 : AES.Word) (by rw [AES.word_card]; norm_num)
        (blockType i).1 (blockType i).2)
    rw [operator_compose] at h
    exact congrArg (fun L => L v) h
  remainder_invisible := by
    intro v i
    have h := congrArg (fun K : AES.WordState → AES.WordState → ℝ => kernelOperator K)
      (physical_remainder_invisible i)
    rw [operator_compose, operator_compose, operator_zero] at h
    exact congrArg (fun L => L v) h

def system : AESRound.OperatorBridge.ProjectionSystem (Fin 14) State :=
  decomposition.toProjectionSystem isLow

theorem step_eq_physical (i j : Fin 14) :
    system.step i j = kernelOperator (physicalBlock i j) := by
  change (kernelOperator (projectionKernel i)).comp
    ((kernelOperator centeredWordStepKernel).comp (kernelOperator (projectionKernel j))) = _
  rw [← operator_compose, ← operator_compose]
  rfl

theorem low_eq_physical (i j : Fin 14) :
    system.low i j = if isLow j then kernelOperator (physicalBlock i j) else 0 := by
  change (if isLow j then decomposition.step i j else 0) = _
  change (if isLow j then system.step i j else 0) = _
  rw [step_eq_physical]

def highKernel (y x : AES.WordState) : ℝ :=
  ∑ k : Fin 14, if isLow k then 0 else projectionKernel k y x

theorem highProject_eq_kernel :
    decomposition.highProject isLow = kernelOperator highKernel := by
  change decomposition.highProject isLow =
    kernelOperator (fun y x => ∑ k : Fin 14, if isLow k then 0 else projectionKernel k y x)
  rw [operator_sum]
  unfold AESRound.ProjectionAssembly.Decomposition.highProject
  apply Finset.sum_congr rfl
  intro k _
  cases h : isLow k
  · simp [h, decomposition]
  · simp only [h, if_true]
    ext f y
    simp [kernelOperator_apply, action]

def returnKernel (i j : Fin 14) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (projectionKernel i)
    (kernelCompose centeredWordStepKernel
      (kernelCompose highKernel (kernelCompose centeredWordStepKernel (projectionKernel j))))

theorem return_eq_physical (i j : Fin 14) :
    system.ret i j = kernelOperator (returnKernel i j) := by
  change (kernelOperator (projectionKernel i)).comp
    ((kernelOperator centeredWordStepKernel).comp
      ((decomposition.highProject isLow).comp
        ((kernelOperator centeredWordStepKernel).comp (kernelOperator (projectionKernel j))))) = _
  rw [highProject_eq_kernel]
  simp only [returnKernel, operator_compose]

theorem step_identity (v : State) (i : Fin 14) :
    system.project i (system.update v) =
      ∑ j, system.step i j (system.project j v) := system.step_identity v i

theorem memory_identity (v : State) (i : Fin 14) :
    system.project i (system.update (system.update v)) =
      (∑ j, system.low i j (system.project j (system.update v))) +
        ∑ j, system.ret i j (system.project j v) := system.memory_identity v i

end AESConcrete.PhysicalProjectionSystem
