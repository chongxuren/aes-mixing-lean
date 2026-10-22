import AES8.Math.PaperActivityInputAnalysis
import AES8.Reductions.Return.PaperAESActivityInputJoin

/-! Physical frame analysis of the actual grouped AES step. This equality
is stated on arbitrary signed input-frame coefficients, before norm bounds. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputPhysical
open AESMixing WordActivityFrame PaperActivityInputCoordinates
open PaperActivityInputAnalysis PaperActivityMinorTransport PaperActivityInputAssembly
open PaperAESActivityIdentification PaperAESActivityInputJoin
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem action_scale {X Y : Type*} [Fintype X] (K : Y → X → ℝ)
    (a : ℝ) (f : X → ℝ) : action K (fun x => a * f x) = fun y => a * action K f y := by
  funext y
  unfold action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def truthSet (u : Fin 4 → Bool) : Finset (Fin 4) :=
  Finset.univ.filter (fun k => u k = true)

theorem truthSet_bit (u : Fin 4 → Bool) (k : Fin 4) :
    decide (k ∈ truthSet u) = u k := by
  cases h : u k <;> simp [truthSet,h]

theorem analysis_actualStep (O : Finset (Fin 4)) (u : Fin 4 → Bool)
    (adjoint : Bool) (y : O → AES.Word) (x : AES.WordState) :
    kernelCompose (analysis O u) (actualStep adjoint) y x =
      ∏ k : Fin 4, if h : k ∈ O then
        AESConcrete.WordFourierVariants.baseResidual adjoint (y ⟨k,h⟩)
          (AESConcrete.WordCrossZero.wordMixAddEquiv x k)
        else wordFrame 0 (u k) (AESConcrete.WordCrossZero.wordMixAddEquiv x k) := by
  change kernelCompose (analysis O u) (coordinateKernel (fun _ : Fin 4 => channel adjoint))
    y (AESConcrete.WordCrossZero.wordMixAddEquiv x) = _
  rw [analysis_channel O u _ (fun _ => channel_pointed adjoint),channel_residual]

theorem analysis_step_frame (O : Finset (Fin 4)) (u b : Fin 4 → Bool)
    (adjoint : Bool) (y : O → AES.Word) :
    action (analysis O u) (action (actualStep adjoint) (frameColumn 0 b)) y =
      frameResponse O (truthSet u) (truthSet b) adjoint y := by
  rw [← kernelCompose_action]
  unfold action frameResponse
  simp_rw [analysis_actualStep,truthSet_bit]
  apply Finset.sum_congr rfl
  intro x _
  rw [product_retained O
    (fun p => AESConcrete.WordFourierVariants.baseResidual adjoint
      (y p) (AESConcrete.WordCrossZero.wordMixAddEquiv x p.val))
    (fun k => wordFrame 0 (u k) (AESConcrete.WordCrossZero.wordMixAddEquiv x k))]
  rfl

/-- The actual projected output analysis is the matrix of actual graph
responses applied to the arbitrary signed activity coefficients. -/
theorem projected_step_analysis (O : Finset (Fin 4))
    (a : ↥(Oᶜ) → Bool) (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ)
    (y : O → AES.Word) :
    partialAnalysis 0 O
      (action (productProjection 0 (residualMask O))
        (action (actualStep adjoint) (synthesize c))) a y =
      ∑ b, c b * frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y := by
  rw [partialAnalysis_projected AESConcrete.AES.word_card_gt_one]
  unfold synthesize
  have he : (fun x : AES.WordState => ∑ b, frameColumn 0 b x * c b) =
      fun x => ∑ b, c b * frameColumn 0 b x := by
    funext x; simp only [mul_comm]
  rw [he,action_sum_family]
  simp_rw [action_scale]
  rw [action_sum_family]
  simp_rw [action_scale,analysis_step_frame]

end AES8.PaperAESActivityInputPhysical
