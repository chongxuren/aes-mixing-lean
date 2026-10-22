/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ReturnCentering
import AES8.Reductions.Return.MiddleFrameExpansion
import AESConcrete.FourResidualStep

/-!
# Literal physical middle kernels

A pointed bistochastic word channel fixes each activity-frame vector.
Composing a middle frame atom with the parallel channel therefore replaces
its three residual projections by actual residual channels, while retaining
both activity vectors. This yields an exact physical return kernel with two
forward AES boundaries and the shared inverse coefficient occurring once.
All identities act on arbitrary signed joint input; no norm cap is assumed.
Constructive proofs only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.PhysicalMiddleKernel
open AESMixing AESMixing.AES
open AES8.WordActivityFrame (wordFrame wordInverse)
open AES8.MiddleFrameExpansion (frameAtom allResidualKernel)

section Generic
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A frame vector is fixed by the transposed channel as well. -/
theorem frame_left_fixed (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (s : Bool) (x : V) :
    (∑ v, wordFrame z s v * D v x) = wordFrame z s x := by
  cases s
  · simp [wordFrame, identityKernel, hD.zero_row]
  · change (∑ v, WordActivityFrame.xi V * D v x) = WordActivityFrame.xi V
    rw [← Finset.mul_sum, hD.column_sum, _root_.mul_one]

def framePair (z : V) (s t : Bool) (y x : V) : ℝ :=
  wordFrame z s y * wordFrame z t x

theorem framePair_compose (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (s t : Bool) :
    kernelCompose (framePair z s t) D = framePair z s t := by
  funext y x
  change (∑ v, (wordFrame z s y * wordFrame z t v) * D v x) = _
  simp_rw [_root_.mul_assoc]
  rw [← Finset.mul_sum, frame_left_fixed D z hD]
  rfl

theorem frameAtom_coordinates (z : V) (c : Fin 4) (s t : Bool) :
    frameAtom z c s t = coordinateKernel (fun i : Fin 4 =>
      if i = c then framePair z s t else residualProjection z) := by
  funext y x
  fin_cases c <;>
    simp [frameAtom, MiddleFrameExpansion.residualTail, coordinateKernel,
      framePair, Fin.prod_univ_four] <;> ring

/-- The actual word residual channel at the three middle residual positions. -/
def channelFrameAtom (D : V → V → ℝ) (z : V) (c : Fin 4) (s t : Bool) :=
  coordinateKernel (fun i : Fin 4 =>
    if i = c then framePair z s t else residualMatrix D z)

theorem frameAtom_compose_parallel (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (c : Fin 4) (s t : Bool) :
    kernelCompose (frameAtom z c s t) (coordinateKernel (fun _ : Fin 4 => D)) =
      channelFrameAtom D z c s t := by
  rw [frameAtom_coordinates, coordinateKernel_compose]
  unfold channelFrameAtom
  congr 1
  funext i
  by_cases hi : i = c
  · simp only [hi, if_true]
    exact framePair_compose D z hD s t
  · simp only [hi, if_false]
    exact AESConcrete.FourResidualStep.pointed_residual_left D z hD

theorem allResidual_compose_parallel (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) :
    kernelCompose (allResidualKernel z) (coordinateKernel (fun _ : Fin 4 => D)) =
      coordinateKernel (fun _ : Fin 4 => residualMatrix D z) := by
  change kernelCompose (coordinateKernel (fun _ : Fin 4 => residualProjection z))
    (coordinateKernel (fun _ : Fin 4 => D)) = _
  rw [coordinateKernel_compose]
  congr 1
  funext i
  exact AESConcrete.FourResidualStep.pointed_residual_left D z hD

/-- Exact kernel entry after composing the high middle projection with H. -/
theorem high_compose_parallel (D : V → V → ℝ) (z : V)
    (hV : 1 < Fintype.card V) (hD : PointedBistochastic D z)
    (y x : Fin 4 → V) :
    kernelCompose (degreeKernel z 3 + degreeKernel z 4)
        (coordinateKernel (fun _ : Fin 4 => D)) y x =
      (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse V s t * channelFrameAtom D z c s t y x) +
      coordinateKernel (fun _ : Fin 4 => residualMatrix D z) y x := by
  change action (degreeKernel z 3 + degreeKernel z 4)
    (fun v => coordinateKernel (fun _ : Fin 4 => D) v x) y = _
  rw [kernel_action_add, degreeKernel_action, degreeKernel_action,
    MiddleFrameExpansion.degree_three_action z hV,
    MiddleFrameExpansion.degree_four_action]
  change (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
      wordInverse V s t *
        kernelCompose (frameAtom z c s t) (coordinateKernel (fun _ : Fin 4 => D)) y x) +
    kernelCompose (allResidualKernel z) (coordinateKernel (fun _ : Fin 4 => D)) y x = _
  simp only [frameAtom_compose_parallel D z hD, allResidual_compose_parallel D z hD]

/-- Keep the finite-sum relabeling abstract before specializing to AES. -/
theorem high_compose_relabel (D : V → V → ℝ) (z : V)
    (hV : 1 < Fintype.card V) (hD : PointedBistochastic D z)
    (e : (Fin 4 → V) → (Fin 4 → V)) :
    kernelCompose (degreeKernel z 3 + degreeKernel z 4)
        (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (e x)) =
      fun y x => (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse V s t * channelFrameAtom D z c s t y (e x)) +
      coordinateKernel (fun _ : Fin 4 => residualMatrix D z) y (e x) := by
  funext y x
  exact high_compose_parallel D z hV hD y (e x)

end Generic

/-- The shortened physical middle kernel still uses the forward AES boundary. -/
def middlePhysicalKernel (y x : WordState) : ℝ :=
  (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
    wordInverse AES.Word s t * channelFrameAtom AES.wordSuperboxKernel 0 c s t y
      (AESConcrete.WordCrossZero.wordMixAddEquiv x)) +
    AESConcrete.FourResidualStep.residualTensor y
      (AESConcrete.WordCrossZero.wordMixAddEquiv x)

theorem high_compose_wordStep :
    kernelCompose (degreeKernel (0 : AES.Word) 3 + degreeKernel (0 : AES.Word) 4)
      AESConcrete.WordStepZeros.wordStepKernel = middlePhysicalKernel := by
  exact high_compose_relabel AES.wordSuperboxKernel (0 : AES.Word)
    SupportProfile.word_card_gt_one AES.word_superbox_pointed
    AESConcrete.WordCrossZero.wordMixAddEquiv

/-- Both physical steps remain, with all middle channel factors explicit. -/
theorem physicalReturnKernel_eq :
    ReturnCentering.physicalReturnKernel =
      kernelCompose AESConcrete.WordStepZeros.wordStepKernel middlePhysicalKernel := by
  unfold ReturnCentering.physicalReturnKernel
  rw [high_compose_wordStep]

theorem highReturn_eq_physical_middle (f : WordState → ℝ) :
    TransferAssembly.highReturn f =
      action AESConcrete.WordStepZeros.wordStepKernel (action middlePhysicalKernel f) := by
  rw [ReturnCentering.highReturn_eq_physical_action, physicalReturnKernel_eq,
    kernelCompose_action]

/-- Literal two-forward-boundary integral kernel before outside projections.
This exact identity is available to marked-code factorization arguments. -/
theorem physicalReturnKernel_entry (y x : WordState) :
    ReturnCentering.physicalReturnKernel y x =
      ∑ v : WordState,
        AES.parallelSuperboxKernel y (AESConcrete.WordCrossZero.wordMixAddEquiv v) *
          middlePhysicalKernel v x := by
  rw [physicalReturnKernel_eq]
  rfl

end AES8.PhysicalMiddleKernel
