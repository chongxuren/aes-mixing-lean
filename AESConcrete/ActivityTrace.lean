import AESConcrete.ActivityTensorContraction
import AESConcrete.ActivityWordKernel
import AESConcrete.WordDegreeOperator
import AESMixing.CenteredActivityGram

/-!
# Semantic activity-trace reduction

The actual centered degree-(0,0) word block is reduced to a sixteen-by-
sixteen inverse-frame trace. Input frame columns are normalized explicitly;
the centered activity Gram uses the existing unnormalized support columns.
Exact rational evaluation of this small scalar expression is separate.
No desired trace or block-energy estimate is assumed. Constructive scope
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityTrace
open AESMixing AESMixing.AES
open AESConcrete.ActivityFrame AESConcrete.ActivityTensorContraction
open AESConcrete.HilbertSchmidtEnergy (hs hs_sq)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel word_kernel_pointed)

set_option maxRecDepth 100000

section GenericTrace
variable {I V Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Zero V] [DecidableEq V] [Fintype Y]

theorem row_contraction (B : Y → (I → V) → ℝ) (y : Y) (s : I → Bool) :
    tensorContraction (B y) s = action B (frameColumn s) y := by
  unfold tensorContraction action
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A right activity projection is sufficient; no output-range assumption
or energy bound is needed for this Hilbert--Schmidt trace identity. -/
theorem frame_trace_rows (hV : Fintype.card V = 256)
    (B : Y → (I → V) → ℝ)
    (hB : ∀ y, action (coordinateKernel (fun _ : I => activityMatrix (0 : V)))
      (B y) = B y) :
    hs B ^ 2 = ∑ s : I → Bool, ∑ t : I → Bool,
      frameInverse s t * gram (fun y s => action B (frameColumn s) y) s t := by
  rw [hs_sq]
  have h := fixed_family_inner hV B B hB hB
  simpa only [pow_two, row_contraction, gram] using h

end GenericTrace

section FourCoordinates
variable {V Y : Type*} [Fintype V] [Zero V] [DecidableEq V] [Fintype Y]

def maskInverse (A B : Fin 16) : ℝ := frameInverse (maskBit A) (maskBit B)

theorem frame_trace_masks (hV : Fintype.card V = 256)
    (B : Y → (Fin 4 → V) → ℝ)
    (hB : ∀ y, action (coordinateKernel (fun _ : Fin 4 => activityMatrix (0 : V)))
      (B y) = B y) :
    hs B ^ 2 = ∑ A : Fin 16, ∑ C : Fin 16,
      maskInverse A C *
        gram (fun y A => action B (frameColumn (maskBit A)) y) A C := by
  rw [frame_trace_rows hV B hB]
  rw [← maskBitsEquiv.sum_comp (fun s => ∑ t : Fin 4 → Bool,
    frameInverse s t * gram (fun y s => action B (frameColumn s) y) s t)]
  apply Finset.sum_congr rfl
  intro A _
  rw [← maskBitsEquiv.sum_comp (fun t =>
    frameInverse (maskBitsEquiv A) t *
      gram (fun y s => action B (frameColumn s) y) (maskBitsEquiv A) t)]
  rfl

def activityBlock (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (kernelCompose (degreeKernel 0 0) (residualMatrix K 0)) (degreeKernel 0 0)

theorem activityBlock_action (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (f : (Fin 4 → V) → ℝ) :
    action (activityBlock K) f =
      degreeComponent 0 0 (action (residualMatrix K 0) (degreeComponent 0 0 f)) := by
  simp only [activityBlock, kernelCompose_action, degreeKernel_action]

theorem activityBlock_eq_degreeBlock (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) :
    activityBlock K = DegreeHilbertSchmidt.block 0 (residualMatrix K 0) 0 0 := by
  apply kernel_action_ext
  intro f
  simp only [activityBlock_action, DegreeHilbertSchmidt.block_action]

theorem degree_zero_idempotent (hV : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    degreeComponent 0 0 (degreeComponent 0 0 f) = degreeComponent 0 0 f := by
  simp only [← degreeKernel_action, ← kernelCompose_action,
    degreeKernel_compose (0 : V) hV]

theorem activityBlock_row_fixed (hV : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (y : Fin 4 → V) :
    action (coordinateKernel (fun _ : Fin 4 => activityMatrix (0 : V)))
      (activityBlock K y) = activityBlock K y := by
  have hr : activityBlock K y =
      degreeComponent 0 0 (kernelCompose (degreeKernel 0 0) (residualMatrix K 0) y) := by
    funext x
    exact DegreeHilbertSchmidt.right_block_row 0 _ 0 y x
  have hp : coordinateKernel (fun _ : Fin 4 => activityMatrix (0 : V)) =
      degreeKernel 0 0 := by rw [degreeKernel_zero]; rfl
  rw [hp, degreeKernel_action, hr]
  exact degree_zero_idempotent hV _

theorem degree_zero_residual_commute (hV : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    degreeComponent 0 0 (wordResidual 0 f) = wordResidual 0 (degreeComponent 0 0 f) := by
  have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
    degree_zero_pointed (0 : V) hV
  simpa only [degreeKernel_action] using (WordDegreeOperator.pointed_residual_commute hp f).symm

theorem action_div {X Z : Type*} [Fintype X]
    (K : Z → X → ℝ) (f : X → ℝ) (c : ℝ) :
    action K (fun x => f x / c) = fun y => action K f y / c := by
  funext y
  simp only [action, ← mul_div_assoc, ← Finset.sum_div]

theorem degree_zero_div (f : (Fin 4 → V) → ℝ) (c : ℝ) :
    degreeComponent 0 0 (fun x => f x / c) = fun y => degreeComponent 0 0 f y / c := by
  simp only [← degreeKernel_action]
  exact action_div _ f c

theorem wordResidual_div {X : Type*} [Fintype X] [DecidableEq X]
    (z : X) (f : X → ℝ) (c : ℝ) :
    wordResidual z (fun x => f x / c) = fun y => wordResidual z f y / c := by
  simp only [← residualProjection_action]
  exact action_div _ f c

end FourCoordinates

section Actual
abbrev Byte := BinaryWord 8
abbrev Word := Fin 4 → Byte

theorem substitution_activity_action {D : Byte → Byte → ℝ}
    (hD : ByteResources D) (f : Word → ℝ) :
    degreeComponent 0 0 (action (substitutionKernel D) f) = degreeComponent 0 0 f := by
  simp only [← degreeKernel_action, degreeKernel_zero, ← kernelCompose_action]
  rw [substitution_pattern_left hD]
  rfl

theorem actual_projected_word_frame (left right : Orientation) (inverse : Bool)
    (A : Fin 16) :
    degreeComponent 0 0 (action (wordKernel left right inverse) (frameColumn (maskBit A))) =
      degreeComponent 0 0 (fun x : Word =>
        frameColumn (maskBit A) ((byteDiffusionOrientation inverse).symm x)) := by
  rw [wordKernel, twoSubstitutionKernel_action,
    ActivityWordKernel.substitution_frame_fixed (channel_resources right),
    substitution_activity_action (channel_resources left)]

/-- All actual substitutions disappear on the activity compression. The
remaining response is the existing centered MDS activity vector, divided
by its explicit input-frame normalizer. -/
theorem actual_activityBlock_frame (left right : Orientation) (inverse : Bool)
    (A : Fin 16) :
    action (activityBlock (wordKernel left right inverse)) (frameColumn (maskBit A)) =
      fun y : Word => centeredActivityResponse (byteDiffusionOrientation inverse) A y /
        (16 : ℝ)^maskSize A := by
  have hb : 1 < Fintype.card Byte := by norm_num [BinaryWord.card]
  rw [activityBlock_action, ActivityWordKernel.frame_degree_zero hb,
    residualMatrix_action (word_kernel_pointed left right inverse),
    ← WordDegreeOperator.pointed_residual_commute (word_kernel_pointed left right inverse),
    degree_zero_residual_commute hb, actual_projected_word_frame]
  have hf : frameColumn (maskBit A) =
      fun x : Word => activityColumn A x / (16 : ℝ)^maskSize A :=
    funext (frameColumn_activity A)
  rw [hf]
  change wordResidual 0 (degreeComponent 0 0 (fun x : Word =>
    diffusedActivityColumn (byteDiffusionOrientation inverse) A x / (16 : ℝ)^maskSize A)) = _
  rw [degree_zero_div, wordResidual_div]
  rfl

theorem actual_activityBlock_frame_gram (left right : Orientation) (inverse : Bool)
    (A B : Fin 16) :
    gram (fun y A => action (activityBlock (wordKernel left right inverse))
      (frameColumn (maskBit A)) y) A B =
      gram (fun y A => centeredActivityResponse (byteDiffusionOrientation inverse) A y) A B /
        ((16 : ℝ)^maskSize A * (16 : ℝ)^maskSize B) := by
  unfold gram
  simp_rw [actual_activityBlock_frame]
  simp only [div_mul_div_comm, ← Finset.sum_div]

/-- Input is the unnormalized raw activity Gram. Rational evaluation of
this finite scalar expression is intentionally a separate certificate. -/
def traceForm (M : Fin 16 → Fin 16 → ℝ) : ℝ :=
  ∑ A : Fin 16, ∑ B : Fin 16, maskInverse A B *
    (M A B - invariantActivityGram 256 A B) /
      ((16 : ℝ)^maskSize A * (16 : ℝ)^maskSize B)

def rawActivityGram (inverse : Bool) (A B : Fin 16) : ℝ :=
  gram (fun y A => degreeComponent 0 0
    (diffusedActivityColumn (byteDiffusionOrientation inverse) A) y) A B

/-- The actual centered degree-(0,0) Hilbert--Schmidt square is a finite
inverse-frame trace with no operator-norm or trace premise. -/
theorem actual_activityBlock_trace (left right : Orientation) (inverse : Bool) :
    hs (activityBlock (wordKernel left right inverse)) ^ 2 = traceForm (rawActivityGram inverse) := by
  rw [frame_trace_masks (by norm_num [BinaryWord.card]) _
    (activityBlock_row_fixed (by norm_num [BinaryWord.card]) _)]
  simp_rw [actual_activityBlock_frame_gram,
    centered_activity_gram (by norm_num [BinaryWord.card]) _
      (byteDiffusionOrientation_zero inverse)]
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  unfold traceForm rawActivityGram
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem actual_degree_zero_trace (left right : Orientation) (inverse : Bool) :
    hs (DegreeHilbertSchmidt.block 0 (residualMatrix (wordKernel left right inverse) 0) 0 0)^2 =
      traceForm (rawActivityGram inverse) := by
  rw [← activityBlock_eq_degreeBlock]
  exact actual_activityBlock_trace left right inverse

end Actual

end AESConcrete.ActivityTrace
