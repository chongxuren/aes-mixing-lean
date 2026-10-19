import AESConcrete.WordFourierCore
import AESConcrete.WordFourierDiffusion
import AESConcrete.WordOrientationClosure

/-!
# Exact whole-word Fourier correspondence

The tensor Fourier transform, actual inverse-transpose diffusion and physical
coordinate reversal identify the entire word kernel. The word activity
projection is transported separately before centering. This is an equality
of matrices, not an assumption of Fourier invariance of entrywise bounds.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordFourierClosure
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.FourierLineOverlap (fourierMate)
open AESConcrete.WordFourierCore
open AESConcrete.WordFourierDiffusion

def reverseKernel (T : AES.Word → AES.Word → ℝ) : AES.Word → AES.Word → ℝ :=
  fun y x => T (wordReverse y) (wordReverse x)

theorem substitution_reverse (D : BinaryWord 8 → BinaryWord 8 → ℝ)
    (y x : AES.Word) :
    substitutionKernel D (wordReverse y) (wordReverse x) = substitutionKernel D y x := by
  change (∏ i : Fin 4, D (y (byteReverse i)) (x (byteReverse i))) =
    ∏ i : Fin 4, D (y i) (x i)
  exact Equiv.prod_comp byteReverse (fun i => D (y i) (x i))

theorem substitution_reverse_left (D : BinaryWord 8 → BinaryWord 8 → ℝ)
    (y x : AES.Word) :
    substitutionKernel D (wordReverse y) x = substitutionKernel D y (wordReverse x) := by
  simpa only [wordReverse_self] using substitution_reverse D y (wordReverse x)

theorem twoSubstitution_as_compose (D E : BinaryWord 8 → BinaryWord 8 → ℝ)
    (L : Equiv.Perm AES.Word) :
    twoSubstitutionKernel D E L = kernelCompose (substitutionKernel D)
      (kernelCompose (permutationKernel L) (substitutionKernel E)) := by
  apply kernel_action_ext
  intro f
  rw [twoSubstitutionKernel_action, kernelCompose_action, kernelCompose_action,
    permutationKernel_action]

theorem twoSubstitution_dual_reverse (D E : BinaryWord 8 → BinaryWord 8 → ℝ)
    (inverse : Bool) :
    twoSubstitutionKernel D E (dualDiffusion inverse) =
      reverseKernel (twoSubstitutionKernel D E (byteDiffusionOrientation (!inverse))) := by
  funext y x
  unfold reverseKernel twoSubstitutionKernel kernelCompose
  have hsum := Equiv.sum_comp wordReverse (fun z =>
    substitutionKernel D y z * substitutionKernel E ((dualDiffusion inverse).symm z) x)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro z _
  rw [dualDiffusion_symm_apply, wordReverse_self, ← substitution_reverse_left,
    substitution_reverse_left E]
  have hL : (byteDiffusionOrientation (!inverse)).symm = byteDiffusionOrientation inverse := by
    cases inverse <;> rfl
  rw [hL]

theorem wordKernel_fourier (left right : Orientation) (inverse : Bool) :
    wordConjugate (wordKernel left right inverse) =
      reverseKernel (wordKernel (fourierMate left) (fourierMate right) (!inverse)) := by
  change wordConjugate (twoSubstitutionKernel (channel left) (channel right)
    (byteDiffusionOrientation inverse)) = _
  rw [twoSubstitution_as_compose, wordConjugate_compose, wordConjugate_compose,
    wordConjugate_substitution, wordConjugate_substitution, wordConjugate_diffusion,
    ← twoSubstitution_as_compose, twoSubstitution_dual_reverse]
  rfl

theorem reverse_activity : reverseKernel (activityMatrix (0 : AES.Word)) = activityMatrix 0 := by
  funext y x
  have hz : wordReverse (0 : AES.Word) = 0 := by rfl
  have hy : wordReverse y = 0 ↔ y = 0 := by
    constructor
    · intro h
      exact wordReverse.injective (h.trans hz.symm)
    · intro h
      rw [h, hz]
  have hx : wordReverse x = 0 ↔ x = 0 := by
    constructor
    · intro h
      exact wordReverse.injective (h.trans hz.symm)
    · intro h
      rw [h, hz]
  simp only [reverseKernel, activityMatrix, hy, hx]

theorem residual_fourier (left right : Orientation) (inverse : Bool) :
    wordConjugate (residualMatrix (wordKernel left right inverse) 0) =
      reverseKernel (residualMatrix
        (wordKernel (fourierMate left) (fourierMate right) (!inverse)) 0) := by
  change wordConjugate (wordKernel left right inverse - activityMatrix (0 : AES.Word)) = _
  rw [wordConjugate_sub, wordKernel_fourier, word_activity_fourier_fixed]
  have hp := reverse_activity
  funext y x
  have h := congrFun (congrFun hp y) x
  change activityMatrix 0 (wordReverse y) (wordReverse x) = activityMatrix 0 y x at h
  change _ - activityMatrix 0 y x = _ - activityMatrix 0 (wordReverse y) (wordReverse x)
  rw [h]
  rfl

end AESConcrete.WordFourierClosure
