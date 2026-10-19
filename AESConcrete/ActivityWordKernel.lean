import AESConcrete.ActivityGraphContraction
import AESConcrete.WordOrientationClosure
import AESMixing.ResidualCoordinates

/-!
# Actual projected word kernels on the normalized activity frame

Every pointed byte channel fixes the two normalized activity columns. The
first substitution therefore disappears on each input frame column. After
an output pattern projection, the second substitution is exactly the tensor
of residual and activity byte pieces evaluated on the actual diffusion.
Positive output patterns also annihilate the whole-word activity projection,
so the same identity holds for the centered word residual kernel.

These are semantic identities, not degree-three norm estimates. Constructive
scope only; no attacks, manuscript edits, or changes to historical sources.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityWordKernel
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ActivityFrame
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel)

section Generic
variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

theorem pointed_byteFrame_fixed {D : V → V → ℝ}
    (hD : PointedBistochastic D 0) (b : Bool) :
    action D (byteFrame b) = byteFrame b := by
  funext y
  cases b
  · simp only [action, byteFrame, Bool.false_eq_true, if_false, identityKernel,
      mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hD.zero_column]
  · simp only [action, byteFrame, if_true, ← Finset.sum_mul, hD.row_sum, one_mul]

theorem coordinate_frame_fixed {I : Type*} [Fintype I] [DecidableEq I]
    (D : I → V → V → ℝ) (hD : ∀ i, PointedBistochastic (D i) 0)
    (a : I → Bool) :
    action (coordinateKernel D) (frameColumn a) = frameColumn a := by
  funext y
  unfold action coordinateKernel frameColumn
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => D i (y i) x * byteFrame (a i) x)]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (pointed_byteFrame_fixed (hD i) (a i)) (y i)

theorem frame_degree_zero (hV : 1 < Fintype.card V) (a : Fin 4 → Bool) :
    degreeComponent (0 : V) 0 (frameColumn a) = frameColumn a := by
  rw [← degreeKernel_action, degreeKernel_zero]
  exact coordinate_frame_fixed (fun _ => activityMatrix 0)
    (fun _ => activityMatrix_pointed 0 hV) a

/-- Any positive residual pattern kills the whole-word activity kernel. -/
theorem pattern_word_activity_zero (hV : 1 < Fintype.card V)
    (a : Fin 4 → Bool) (k : Fin 4) (hk : a k = true) :
    kernelCompose (productProjection (0 : V) a)
      (activityMatrix (0 : Fin 4 → V)) = 0 := by
  have hr : kernelCompose (activityMatrix (0 : Fin 4 → V))
      (productProjection (0 : V) a) = 0 := by
    apply kernel_action_ext
    intro f
    rw [kernelCompose_action, activityMatrix_action]
    have hz := productProjection_marked_zero (0 : V) a k hk f (0 : Fin 4 → V) rfl
    have hs := productProjection_marked_sum (0 : V) hV a k hk f
    rw [zero_kernel_action]
    funext y
    change wordAverage (0 : Fin 4 → V) (action (productProjection (0 : V) a) f) y = 0
    simp only [wordAverage, nonzeroMean, hz, hs, sub_self, zero_div, ite_self]
  funext y x
  change (∑ v, productProjection (0 : V) a y v * activityMatrix (0 : Fin 4 → V) v x) = 0
  have h := congrFun (congrFun hr x) y
  change (∑ v, activityMatrix (0 : Fin 4 → V) x v * productProjection (0 : V) a v y) = 0 at h
  calc
    _ = ∑ v, activityMatrix (0 : Fin 4 → V) x v * productProjection (0 : V) a v y := by
      apply Finset.sum_congr rfl
      intro v _
      rw [productProjection_symmetric (0 : V) a y v,
        activityMatrix_symmetric (0 : Fin 4 → V) v x]
      ring
    _ = 0 := h

theorem centered_pattern_action (hV : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (a : Fin 4 → Bool) (k : Fin 4) (hk : a k = true)
    (f : (Fin 4 → V) → ℝ) :
    action (productProjection 0 a) (action (residualMatrix K 0) f) =
      action (productProjection 0 a) (action K f) := by
  change action (productProjection 0 a) (action (K - activityMatrix 0) f) = _
  rw [kernel_action_sub, action_sub,
    ← kernelCompose_action (productProjection (0 : V) a) (activityMatrix (0 : Fin 4 → V)) f,
    pattern_word_activity_zero hV a k hk]
  simp only [zero_kernel_action, sub_zero]

end Generic

theorem substitution_frame_fixed {D : Byte → Byte → ℝ}
    (hD : ByteResources D) (a : Fin 4 → Bool) :
    action (substitutionKernel D) (frameColumn a) = frameColumn a :=
  coordinate_frame_fixed (fun _ => D) (fun _ => hD.pointed) a

/-- Exact action of a projected two-substitution word on an input frame column. -/
theorem projected_word_frame {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Equiv.Perm (Fin 4 → Byte)) (a out : Fin 16) (y : Fin 4 → Byte) :
    action (productProjection 0 (maskBit out))
      (action (twoSubstitutionKernel D E L) (frameColumn (maskBit a))) y =
      ∑ x : Fin 4 → Byte,
        (∏ i, bytePiece D (maskBit out i) (y i) (L x i)) * frameColumn (maskBit a) x := by
  rw [twoSubstitutionKernel_action, substitution_frame_fixed hE,
    ← kernelCompose_action, substitution_pattern_left hD]
  change (∑ z : Fin 4 → Byte,
    coordinateKernel (fun i => bytePiece D (maskBit out i)) y z *
      frameColumn (maskBit a) (L.symm z)) = _
  have he := Equiv.sum_comp L (fun z =>
    coordinateKernel (fun i => bytePiece D (maskBit out i)) y z *
      frameColumn (maskBit a) (L.symm z))
  simpa only [Equiv.symm_apply_apply, coordinateKernel] using he.symm

/-- Both actual diffusion directions and all explicit byte orientations. -/
theorem actual_projected_word_frame (left right : Orientation) (inverse : Bool)
    (a out : Fin 16) (y : Fin 4 → Byte) :
    action (productProjection 0 (maskBit out))
      (action (wordKernel left right inverse) (frameColumn (maskBit a))) y =
      ∑ x : Fin 4 → Byte,
        (∏ i, bytePiece (channel left) (maskBit out i) (y i)
          (byteDiffusionHom inverse x i)) * frameColumn (maskBit a) x := by
  simp_rw [byteDiffusionHom_apply]
  exact projected_word_frame (channel_resources left) (channel_resources right)
    (byteDiffusionOrientation inverse) a out y

theorem actual_centered_projected_word_frame (left right : Orientation) (inverse : Bool)
    (a out : Fin 16) (k : Fin 4) (hk : maskBit out k = true) (y : Fin 4 → Byte) :
    action (productProjection 0 (maskBit out))
      (action (residualMatrix (wordKernel left right inverse) 0) (frameColumn (maskBit a))) y =
      ∑ x : Fin 4 → Byte,
        (∏ i, bytePiece (channel left) (maskBit out i) (y i)
          (byteDiffusionHom inverse x i)) * frameColumn (maskBit a) x := by
  rw [centered_pattern_action (by norm_num [BinaryWord.card]) _ _ k hk]
  exact actual_projected_word_frame left right inverse a out y

end AESConcrete.ActivityWordKernel
