import AESConcrete.DampedDegreeThree

/-!
# Exact oriented transpose and the reverse damped degree-three block

The transpose correspondence is proved from the actual two-substitution
kernel by reindexing its middle variable through the diffusion permutation.
The existing finite adjoint argument then transfers the proved forward bound
to the actual reverse block. No raw undamped cap or norm-invariance premise
is used. The complete word/round assembly is separate.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ReverseDegreeThree
open AESMixing
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordOrientationClosure (wordKernel)

def transposeOrientation : Orientation → Orientation
  | .ordinary => .transposed
  | .transposed => .ordinary
  | .fourier => .fourierTransposed
  | .fourierTransposed => .fourier

theorem transposeOrientation_twice (o : Orientation) :
    transposeOrientation (transposeOrientation o) = o := by
  cases o <;> rfl

theorem channel_transpose (o : Orientation) :
    channel (transposeOrientation o) = fun y x => channel o x y := by
  cases o <;> rfl

/-- Exact transpose of the concrete two-substitution composition. -/
theorem twoSubstitutionKernel_transpose
    (D E : Byte → Byte → ℝ) (L : Equiv.Perm (Fin 4 → Byte)) :
    (fun y x => twoSubstitutionKernel D E L x y) =
      twoSubstitutionKernel (fun y x => E x y) (fun y x => D x y) L.symm := by
  funext y x
  unfold twoSubstitutionKernel kernelCompose
  calc
    _ = ∑ z : Fin 4 → Byte,
        substitutionKernel D x (L z) * substitutionKernel E z y := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp L (fun z =>
          substitutionKernel D x z * substitutionKernel E (L.symm z) y)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      change substitutionKernel D x (L z) * substitutionKernel E z y =
        substitutionKernel E z y * substitutionKernel D x (L z)
      ring

/-- Equality of the actual oriented word matrices, for all four channels
and both actual diffusion directions. -/
theorem wordKernel_transpose (left right : Orientation) (inverse : Bool) :
    (fun y x => wordKernel left right inverse x y) =
      wordKernel (transposeOrientation right) (transposeOrientation left) (!inverse) := by
  unfold wordKernel
  rw [twoSubstitutionKernel_transpose, channel_transpose, channel_transpose]
  have he : (byteDiffusionOrientation inverse).symm =
      byteDiffusionOrientation (!inverse) := by
    cases inverse <;> rfl
  rw [he]

theorem residual_transpose (left right : Orientation) (inverse : Bool)
    (x y : Fin 4 → Byte) :
    residualMatrix (wordKernel left right inverse) 0 x y =
      residualMatrix
        (wordKernel (transposeOrientation right) (transposeOrientation left) (!inverse)) 0 y x := by
  have h := congrFun (congrFun (wordKernel_transpose left right inverse) y) x
  change wordKernel left right inverse x y =
    wordKernel (transposeOrientation right) (transposeOrientation left) (!inverse) y x at h
  unfold residualMatrix
  rw [h, activityMatrix_symmetric (0 : Fin 4 → Byte) x y]

private theorem kernel_action_inner {V W : Type*} [Fintype V] [Fintype W]
    (K : W → V → ℝ) (f : V → ℝ) (g : W → ℝ) :
    (∑ y : W, action K f y*g y) =
      ∑ x : V, f x*action (fun x y => K y x) g x := by
  simp only [action, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem residual_action_adjoint (left right : Orientation) (inverse : Bool)
    (f g : (Fin 4 → Byte) → ℝ) :
    (∑ y, action (residualMatrix
      (wordKernel (transposeOrientation right) (transposeOrientation left) (!inverse)) 0) f y*g y) =
    ∑ x, f x*action (residualMatrix (wordKernel left right inverse) 0) g x := by
  have he :
      (fun x y => residualMatrix
        (wordKernel (transposeOrientation right) (transposeOrientation left) (!inverse)) 0 y x) =
      residualMatrix (wordKernel left right inverse) 0 := by
    funext x y
    exact (residual_transpose left right inverse x y).symm
  rw [kernel_action_inner, he]

def reverseBlockKernel (left right : Orientation) (inverse : Bool) :
    (Fin 4 → Byte) → (Fin 4 → Byte) → ℝ :=
  kernelCompose (degreeKernel 0 0)
    (kernelCompose (residualMatrix (wordKernel left right inverse) 0) (degreeKernel 0 3))

theorem forward_reverse_adjoint (left right : Orientation) (inverse : Bool)
    (f g : (Fin 4 → Byte) → ℝ) :
    (∑ y, action (DampedDegreeThree.forwardBlockKernel
      (transposeOrientation right) (transposeOrientation left) (!inverse)) f y*g y) =
    ∑ x, f x*action (reverseBlockKernel left right inverse) g x := by
  simp only [DampedDegreeThree.forwardBlockKernel, reverseBlockKernel,
    kernelCompose_action, degreeKernel_action]
  rw [degreeComponent_inner, residual_action_adjoint]
  exact degreeComponent_inner (0 : Byte) 0 f _

theorem reverseBlock_energy (left right : Orientation) (inverse : Bool)
    (f : (Fin 4 → Byte) → ℝ) :
    (∑ y, (action (reverseBlockKernel left right inverse) f y)^2) ≤
      (33 / (10*65536) : ℝ)^2 * ∑ x, (f x)^2 :=
  adjoint_energy_le _ _ (33 / (10*65536))
    (forward_reverse_adjoint left right inverse)
    (DampedDegreeThree.forwardBlock_energy
      (transposeOrientation right) (transposeOrientation left) (!inverse)) f

/-- The projected-input energy is retained for the sharp degree matrix. -/
theorem actual_reverse_degree_three_energy (left right : Orientation) (inverse : Bool)
    (f : (Fin 4 → Byte) → ℝ) :
    (∑ y, (degreeComponent 0 0 (action (residualMatrix (wordKernel left right inverse) 0)
      (degreeComponent 0 3 f)) y)^2) ≤
      (33 / (10*65536) : ℝ)^2 * ∑ x, (degreeComponent 0 3 f x)^2 := by
  have h := reverseBlock_energy left right inverse (degreeComponent 0 3 f)
  simp only [reverseBlockKernel, kernelCompose_action, degreeKernel_action,
    degreeComponent_compose (0 : Byte) (by norm_num [BinaryWord.card]), if_pos rfl] at h
  exact h

theorem reverseBlock_operator_norm (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (reverseBlockKernel left right inverse)‖ ≤ (33 / (10*65536) : ℝ) :=
  kernelOperator_norm_le _ (by norm_num) (reverseBlock_energy left right inverse)

end AESConcrete.ReverseDegreeThree
