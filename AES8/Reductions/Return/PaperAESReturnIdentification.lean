import AES8.Reductions.Return.PaperAESReturnOutside
import AES8.Reductions.Return.PaperAESActivityIdentification
import AES8.Reductions.Return.PaperAESWholeGraph

/-! Literal actual shared-middle return branches equal the canonical graph
return followed by the input residual projection. Constructive identities only;
no norm-resource application, support lift, attack, or final theorem is asserted. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnIdentification
open AESMixing AESMixing.AES
open PaperActivityMinorTransport PaperActivityFrameJoin
open PaperAESActivityIdentification PaperAESFixedStepTransport
open PaperWordGraphDuality PaperWordGraphCode
open AESConcrete.WordCrossZero AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

theorem outside_join_eq_steps {i j m : ℕ} (O I A B M C D : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (em : M ≃ Fin m) :
    outsideContract O I A B eo ei
      (kernelCompose (actualStep false)
        (kernelCompose
          (kernelCompose (synthesis M (fun k => decide (k ∈ C)))
            (analysis M (fun k => decide (k ∈ D)))) (actualStep false))) =
      kernelCompose (contracted O M A C eo em false)
        (contracted M I D B em ei false) := by
  have hj := join_reindexed (V := AES.Word) M em
    (fun k => decide (k ∈ C)) (fun k => decide (k ∈ D))
  unfold outsideContract contracted
  rw [← hj]
  simp only [compose_assoc]

theorem frameReturn_eq_steps (c : Fin 4) (s t : Bool) :
    PhysicalZeroPattern.frameReturnKernel c s t =
      kernelCompose (actualStep false)
        (kernelCompose (MiddleFrameExpansion.frameAtom 0 c s t) (actualStep false)) := by
  have hc := PhysicalMiddleKernel.frameAtom_compose_parallel
    wordSuperboxKernel (0 : AES.Word) word_superbox_pointed c s t
  have he : kernelCompose (MiddleFrameExpansion.frameAtom 0 c s t) (actualStep false) =
      fun y x => PhysicalMiddleKernel.channelFrameAtom wordSuperboxKernel 0 c s t y
        (wordMixAddEquiv x) := by
    funext y x
    simpa only [kernelCompose, actualStep_ordinary,
      AESConcrete.WordStepZeros.wordStepKernel, parallelSuperboxKernel] using
        congrFun (congrFun hc y) (wordMixAddEquiv x)
  rw [he, actualStep_ordinary]
  funext y x
  rfl

/-- Each actual branch is two actual one-step contractions joined by the
same retained middle coordinates. No activity metric is paid here. -/
theorem contractedBranch_eq_steps {i j m : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (c : Fin 4)
    (em : middle c ≃ Fin m) (s t : Bool) :
    contractedBranch O I A B eo ei c s t =
      kernelCompose
        (contracted O (middle c) A (middleUniform c s) eo em false)
        (contracted (middle c) I (middleUniform c t) B em ei false) := by
  unfold contractedBranch
  rw [frameReturn_eq_steps]
  rw [← middle_join c s t]
  exact outside_join_eq_steps O I A B (middle c) (middleUniform c s)
    (middleUniform c t) eo ei em

/-- Right physical graph is enumerated outside first, middle second. -/
def rightEquiv {j m : ℕ} (I M : Finset (Fin 4)) (ei : I ≃ Fin j) (em : M ≃ Fin m) :
    marked M I ≃ Fin j ⊕ Fin m :=
  (markedEquiv M I em ei).trans (Equiv.sumComm _ _)

theorem right_graph {j m : ℕ} (I M A B : Finset (Fin 4))
    (ei : I ≃ Fin j) (em : M ≃ Fin m) :
    physicalGraph (marked M I) (uniform M I A B) (markedEquiv M I em ei) =
      fun x y => graphContraction (marked M I) (uniform M I A B)
        (fun a => Sum.elim y x (rightEquiv I M ei em a)) := by
  funext x y
  unfold physicalGraph rightEquiv
  apply congrArg (graphContraction (marked M I) (uniform M I A B))
  funext a
  cases h : markedEquiv M I em ei a <;> simp [h]

theorem projection_residual (m : ℕ) :
    kernelCompose (P m) (R m false) = R m false := by
  have hp : kernelCompose (residualProjection (0 : AES.Word)) (baseResidual false) =
      baseResidual false := by
    let P : AES.Word → AES.Word → ℝ := residualProjection 0
    have hR : baseResidual false = kernelCompose P wordSuperboxKernel :=
      (PaperActivityMinorTransport.residual_left word_superbox_pointed).symm
    have hP : kernelCompose P P = P := residual_idempotent AESConcrete.AES.word_card_gt_one
    calc
      kernelCompose P (baseResidual false) =
          kernelCompose P (kernelCompose P wordSuperboxKernel) :=
        congrArg (fun K : AES.Word → AES.Word → ℝ => kernelCompose P K) hR
      _ = kernelCompose (kernelCompose P P) wordSuperboxKernel :=
        (compose_assoc P P wordSuperboxKernel).symm
      _ = kernelCompose P wordSuperboxKernel :=
        congrArg (fun K : AES.Word → AES.Word → ℝ => kernelCompose K wordSuperboxKernel) hP
      _ = baseResidual false := hR.symm
  unfold P R
  rw [coordinateKernel_compose]
  apply congrArg coordinateKernel
  funext k
  exact hp

/-- No extra middle projection remains after joining the two actual steps. -/
theorem joinedSteps_eq_physicalReturn {i j m : ℕ} (O I A B M C D : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (em : M ≃ Fin m) :
    kernelCompose (contracted O M A C eo em false)
        (contracted M I D B em ei false) =
      kernelCompose
        (PaperAESWholeGraph.physicalReturn
          (marked O M) (uniform O M A C)
          (marked M I) (uniform M I D B)
          (markedEquiv O M eo em) (rightEquiv I M ei em))
        (P j) := by
  rw [contracted_eq_physicalStep, contracted_eq_physicalStep]
  unfold physicalStep PaperAESWholeGraph.physicalReturn
  rw [right_graph I M D B ei em]
  simp only [← compose_assoc]
  rw [compose_assoc _ (P m) (R m false), projection_residual]
  rfl

/-- Literal graph return, with its genuine input residual projection.
All outside zero/full choices and every omitted middle position are allowed. -/
theorem contractedBranch_eq_physicalReturn {i j m : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (c : Fin 4)
    (em : middle c ≃ Fin m) (s t : Bool) :
    contractedBranch O I A B eo ei c s t =
      kernelCompose
        (PaperAESWholeGraph.physicalReturn
          (marked O (middle c)) (uniform O (middle c) A (middleUniform c s))
          (marked (middle c) I) (uniform (middle c) I (middleUniform c t) B)
          (markedEquiv O (middle c) eo em) (rightEquiv I (middle c) ei em))
        (P j) := by
  rw [contractedBranch_eq_steps O I A B eo ei c em s t]
  exact joinedSteps_eq_physicalReturn O I A B (middle c) (middleUniform c s)
    (middleUniform c t) eo ei em

theorem full_join :
    kernelCompose (synthesis (V := AES.Word) Finset.univ (fun _ => false))
      (analysis Finset.univ (fun _ => false)) = MiddleFrameExpansion.allResidualKernel 0 := by
  funext y x
  rw [join_coordinates _ _ _ AESConcrete.AES.word_card_gt_one]
  simp only [Finset.mem_univ, if_true, MiddleFrameExpansion.allResidualKernel]

theorem fourReturn_eq_steps :
    PhysicalZeroPattern.fourReturnKernel =
      kernelCompose (actualStep false)
        (kernelCompose (MiddleFrameExpansion.allResidualKernel 0) (actualStep false)) := by
  have hc := PhysicalMiddleKernel.allResidual_compose_parallel
    wordSuperboxKernel (0 : AES.Word) word_superbox_pointed
  have he : kernelCompose (MiddleFrameExpansion.allResidualKernel 0) (actualStep false) =
      fun y x => AESConcrete.FourResidualStep.residualTensor y (wordMixAddEquiv x) := by
    funext y x
    simpa only [kernelCompose, actualStep_ordinary,
      AESConcrete.WordStepZeros.wordStepKernel, parallelSuperboxKernel,
      AESConcrete.FourResidualStep.residualTensor] using
        congrFun (congrFun hc y) (wordMixAddEquiv x)
  rw [he, actualStep_ordinary]
  funext y x
  rfl

theorem contractedFour_eq_steps {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (em : (Finset.univ : Finset (Fin 4)) ≃ Fin 4) :
    contractedFour O I A B eo ei =
      kernelCompose (contracted O Finset.univ A ∅ eo em false)
        (contracted Finset.univ I ∅ B em ei false) := by
  unfold contractedFour
  rw [fourReturn_eq_steps, ← full_join]
  simpa using outside_join_eq_steps O I A B Finset.univ ∅ ∅ eo ei em

theorem contractedFour_eq_physicalReturn {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (em : (Finset.univ : Finset (Fin 4)) ≃ Fin 4) :
    contractedFour O I A B eo ei =
      kernelCompose
        (PaperAESWholeGraph.physicalReturn
          (marked O Finset.univ) (uniform O Finset.univ A ∅)
          (marked Finset.univ I) (uniform Finset.univ I ∅ B)
          (markedEquiv O Finset.univ eo em) (rightEquiv I Finset.univ ei em))
        (P j) := by
  rw [contractedFour_eq_steps O I A B eo ei em]
  exact joinedSteps_eq_physicalReturn O I A B Finset.univ ∅ ∅ eo ei em

/-- Kernel equality applies to every complex joint vector without a product,
sign, constancy, or independence premise. -/
theorem contractedBranch_complex_action {i j m : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (c : Fin 4)
    (em : middle c ≃ Fin m) (s t : Bool) (f : (Fin j → AES.Word) → ℂ) :
    PaperKernelBounds.kernelAction
      (fun y x => (contractedBranch O I A B eo ei c s t y x : ℂ)) f =
      PaperKernelBounds.kernelAction (fun y x =>
        (kernelCompose
          (PaperAESWholeGraph.physicalReturn
            (marked O (middle c)) (uniform O (middle c) A (middleUniform c s))
            (marked (middle c) I) (uniform (middle c) I (middleUniform c t) B)
            (markedEquiv O (middle c) eo em) (rightEquiv I (middle c) ei em))
          (P j) y x : ℂ)) f := by
  rw [contractedBranch_eq_physicalReturn O I A B eo ei c em s t]

end AES8.PaperAESReturnIdentification
