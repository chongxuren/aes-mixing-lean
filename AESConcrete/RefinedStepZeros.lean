import AESConcrete.RefinedWordProjection
import AESConcrete.CenteredWordStepZeros

/-! The thirty-two exact-support cross zeros in the fourteen-type model.
Only the degree-zero/degree-one cross family is established here. Nonzero
step caps, return caps and the profile/experiment interface remain separate.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.RefinedStepZeros
open AESMixing RefinedWordProjection CenteredWordStepZeros

theorem refined_sandwich_zero {V : Type*} [Fintype V] [DecidableEq V]
    (P Q E F S : V → V → ℝ)
    (hP : kernelCompose P E = P) (hQ : kernelCompose F Q = Q)
    (hzero : kernelCompose E (kernelCompose S F) = 0) :
    kernelCompose P (kernelCompose S Q) = 0 := by
  calc
    _ = kernelCompose (kernelCompose P E) (kernelCompose S (kernelCompose F Q)) := by
      rw [hP, hQ]
    _ = kernelCompose P (kernelCompose (kernelCompose E (kernelCompose S F)) Q) := by
      simp only [compose_assoc]
    _ = 0 := by
      rw [hzero]
      funext x y
      simp [kernelCompose]

def refinedCenteredBlock (i a j b : Fin 5) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (refinedKernel (0 : AES.Word) i a)
    (kernelCompose centeredWordStepKernel (refinedKernel (0 : AES.Word) j b))

theorem refinedCenteredBlock_zero_one (a b : Fin 5) :
    refinedCenteredBlock 0 a 1 b = 0 := by
  apply refined_sandwich_zero _ _ (degreeKernel (0 : AES.Word) 0)
    (degreeKernel (0 : AES.Word) 1) _
  · exact refinedKernel_compose_degreeKernel 0 (by rw [AES.word_card]; norm_num) 0 a
  · exact degreeKernel_compose_refinedKernel 0 (by rw [AES.word_card]; norm_num) 1 b
  · exact centeredWordStepBlock_zero_one

theorem refinedCenteredBlock_one_zero (a b : Fin 5) :
    refinedCenteredBlock 1 a 0 b = 0 := by
  apply refined_sandwich_zero _ _ (degreeKernel (0 : AES.Word) 1)
    (degreeKernel (0 : AES.Word) 0) _
  · exact refinedKernel_compose_degreeKernel 0 (by rw [AES.word_card]; norm_num) 1 a
  · exact degreeKernel_compose_refinedKernel 0 (by rw [AES.word_card]; norm_num) 0 b
  · exact centeredWordStepBlock_one_zero

/-- The fixed certificate order: (residual words, active words). -/
def blockType : Fin 14 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4),
    (2,2), (2,3), (2,4), (3,3), (3,4), (4,4)]

def physicalBlock (i j : Fin 14) : AES.WordState → AES.WordState → ℝ :=
  refinedCenteredBlock (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2

def crossPair (i j : Fin 14) : Prop :=
  ((blockType i).1 = 0 ∧ (blockType j).1 = 1) ∨
    ((blockType i).1 = 1 ∧ (blockType j).1 = 0)

instance (i j : Fin 14) : Decidable (crossPair i j) := by unfold crossPair; infer_instance

theorem physicalBlock_cross_zero (i j : Fin 14) (h : crossPair i j) :
    physicalBlock i j = 0 := by
  rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · unfold physicalBlock
    rw [hi, hj]
    exact refinedCenteredBlock_zero_one _ _
  · unfold physicalBlock
    rw [hi, hj]
    exact refinedCenteredBlock_one_zero _ _

theorem physicalBlock_cross_norm (i j : Fin 14) (h : crossPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [physicalBlock_cross_zero i j h]
  simp [action]

theorem crossPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => crossPair ij.1 ij.2)).card = 32 := by decide

end AESConcrete.RefinedStepZeros
