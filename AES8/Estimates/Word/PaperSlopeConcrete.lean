import AES8.Estimates.Word.PaperSlopeCriterion
import AES8.Reductions.Graph.PaperSlopeSymbolicEnergy
import AES8.Model.Byte.PaperAESAlgebraic

/-! The symbolic slope certificate discharges the physical criterion, including
the literal AES permutation. Bounds are on actual degree-projected operators. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeConcrete
open AESMixing PaperKernelBounds AESConcrete.DegreeHilbertSchmidt
open AESConcrete.WordFourierDiffusion PaperSlopeSymbolicGraph
set_option autoImplicit false

theorem symbolic_forward_norms {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod 2) F] (a : F)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (hq : Fintype.card F = 256) :
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 2 0)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 2 0)‖ <
      (71/5000 : ℝ)) :=
  ⟨PaperSlopeCriterion.forward_norm_sq_lt hq _ (diffusionEquiv_isMDS a ha)
      (diffusionEquiv_sameSlopeClasses a ha),
    PaperSlopeCriterion.forward_norm_lt hq _ (diffusionEquiv_isMDS a ha)
      (diffusionEquiv_sameSlopeClasses a ha)⟩

theorem symbolic_reversal (a : BinaryWord 8) (i j : Fin 4) :
    PaperSymbolicDiffusion.matrix a (byteReverse i) (byteReverse j) =
      PaperSymbolicDiffusion.matrix a j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem symbolic_fieldMatrix (a : BinaryWord 8)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (x : Fin 4 → BinaryWord 8) :
    diffusionEquiv a ha x = fieldMatrix (PaperSymbolicDiffusion.matrix a) x := rfl

theorem symbolic_norms (a : BinaryWord 8)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 2 0)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 2 0)‖ <
      (71/5000 : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 0 2)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (diffusionEquiv a ha).toEquiv) 0 2)‖ <
      (71/5000 : ℝ)) := by
  have hq : Fintype.card (BinaryWord 8) = 256 := by norm_num [BinaryWord.card]
  obtain ⟨hs,hn⟩ := symbolic_forward_norms a ha hq
  have hr := PaperCirculantReverse.boundary_norm_eq (PaperSymbolicDiffusion.matrix a)
    (diffusionEquiv a ha).toEquiv (symbolic_fieldMatrix a ha) (symbolic_reversal a) 2 0
  exact ⟨hs,hn,by rw [hr]; exact hs,by rw [hr]; exact hn⟩

theorem aes_diffusion_eq :
    (diffusionEquiv PaperAESAlgebraic.generator
      PaperAESAlgebraic.generator_degree_gt_six).toEquiv = byteDiffusionOrientation false := by
  apply Equiv.ext
  intro x
  rw [byteDiffusionOrientation_apply]
  change fieldMatrix (PaperSymbolicDiffusion.matrix PaperAESAlgebraic.generator) x = _
  have hm : PaperSymbolicDiffusion.matrix PaperAESAlgebraic.generator = gramMixing false := by
    funext i j
    exact PaperAESAlgebraic.matrix_is_AES i j
  rw [hm]

/-- The literal AES MixColumns boundary, with no geometric or norm premises. -/
theorem aes_norms :
    (‖kernelOperator (block 0 (permutationKernel (byteDiffusionOrientation false)) 2 0)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (byteDiffusionOrientation false)) 2 0)‖ <
      (71/5000 : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (byteDiffusionOrientation false)) 0 2)‖^2 <
      (66/(5*256^2) : ℝ)) ∧
    (‖kernelOperator (block 0 (permutationKernel (byteDiffusionOrientation false)) 0 2)‖ <
      (71/5000 : ℝ)) := by
  simpa only [aes_diffusion_eq] using
    symbolic_norms PaperAESAlgebraic.generator PaperAESAlgebraic.generator_degree_gt_six

end AES8.PaperSlopeConcrete
