import AES8.Estimates.Transfer.PaperActivityPrintedScalars
import AES8.Reductions.Return.PaperWholeGraphReturn

/-! The printed activity constants for actual physical kernels. Restriction
and complexification preserve the counting Euclidean normalization. The full
Hilbert adjoint is transposed, not an unexplained change of channel flag. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityPhysicalBounds
open AESMixing PaperKernelBounds PaperFiberKernel
open PaperActivityFullCompression PaperActivityPhysicalJoin PaperActivityPrintedScalars
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActivityTrace (activityBlock)
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

section GeneralNorms
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

theorem real_energy_of_norm (K : Y → X → ℝ) (f : X → ℝ) :
    (∑ y, action K f y ^ 2) ≤ ‖kernelOperator K‖^2 * ∑ x, f x^2 := by
  have h := (kernelOperator K).le_opNorm (WithLp.toLp 2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg (kernelOperator K)) (norm_nonneg (WithLp.toLp 2 f)))).mpr h
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply,
    kernelAction, action] using hs

/-- Extending a real kernel to complex inputs preserves its norm bound. -/
theorem complex_norm_le_real (K : Y → X → ℝ) :
    ‖kernelOperator (fun y x => (K y x : ℂ))‖ ≤ ‖kernelOperator K‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact operator_norm_sq_le_of_energy _ _ (sq_nonneg _)
    (PaperWholeGraphReturn.complex_energy_of_real K _ (real_energy_of_norm K))

variable [DecidableEq Y]

theorem transpose_norm (K : Y → X → ℝ) :
    ‖kernelOperator (fun x y => K y x)‖ = ‖kernelOperator K‖ := by
  calc
    _ = ‖(kernelOperator K).adjoint‖ := by rw [kernelOperator_adjoint]; rfl
    _ = _ := ContinuousLinearMap.adjoint.norm_map _

theorem adjoint_norm {𝕜 : Type*} [RCLike 𝕜] (K : Y → X → 𝕜) :
    ‖(kernelOperator K).adjoint‖ = ‖kernelOperator K‖ :=
  ContinuousLinearMap.adjoint.norm_map _

end GeneralNorms

section Restriction
variable {X : Type*} [Fintype X] [DecidableEq X]

def subkernel (z : X) (K : X → X → ℝ) : {x : X // x ≠ z} → {x : X // x ≠ z} → ℝ :=
  fun y x => K y.val x.val

def zeroExtend (z : X) (f : {x : X // x ≠ z} → ℂ) (x : X) : ℂ :=
  if hx : x ≠ z then f ⟨x,hx⟩ else 0

theorem zeroExtend_energy (z : X) (f : {x : X // x ≠ z} → ℂ) :
    (∑ x : X, ‖zeroExtend z f x‖^2) = ∑ x, ‖f x‖^2 := by
  apply Finset.sum_congr_set {x : X | x ≠ z}
  · intro x hx
    change x ≠ z at hx
    simp only [zeroExtend, dif_pos hx]
    rfl
  · intro x hx
    change ¬(x ≠ z) at hx
    simp only [zeroExtend, dif_neg hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem subkernel_action (z : X) (K : X → X → ℝ)
    (f : {x : X // x ≠ z} → ℂ) (y : {x : X // x ≠ z}) :
    kernelAction (fun y x => (K y x : ℂ)) (zeroExtend z f) y.val =
      kernelAction (fun y x => (subkernel z K y x : ℂ)) f y := by
  unfold kernelAction subkernel
  apply Finset.sum_congr_set {x : X | x ≠ z}
  · intro x hx
    change x ≠ z at hx
    simp only [zeroExtend, dif_pos hx]
    rfl
  · intro x hx
    change ¬(x ≠ z) at hx
    simp only [zeroExtend, dif_neg hx, mul_zero]

theorem restrict_energy_le (z : X) (g : X → ℂ) :
    (∑ y : {x : X // x ≠ z}, ‖g y.val‖^2) ≤ ∑ y : X, ‖g y‖^2 := by
  have he : (∑ y : X, if y ≠ z then ‖g y‖^2 else 0) =
      ∑ y : {x : X // x ≠ z}, ‖g y.val‖^2 := by
    apply Finset.sum_congr_set {y : X | y ≠ z}
    · intro y hy
      exact if_pos hy
    · intro y hy
      exact if_neg hy
  rw [← he]
  apply Finset.sum_le_sum
  intro y _
  split_ifs <;> first | exact le_rfl | exact sq_nonneg _

theorem subkernel_complex_norm_le_real (z : X) (K : X → X → ℝ) :
    ‖kernelOperator (fun y x => (subkernel z K y x : ℂ))‖ ≤ ‖kernelOperator K‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply operator_norm_sq_le_of_energy _ _ (sq_nonneg _)
  intro f
  simp_rw [← subkernel_action]
  have h := (restrict_energy_le z (kernelAction (fun y x => (K y x : ℂ))
    (zeroExtend z f))).trans
      (PaperWholeGraphReturn.complex_energy_of_real K _ (real_energy_of_norm K) (zeroExtend z f))
  simpa only [zeroExtend_energy] using h

end Restriction

/-- Exact ordinary grouped step, before discarding the fixed zero state. -/
theorem word_activity_kernel_eq :
    AESConcrete.CenteredWordStepZeros.centeredWordStepBlock 0 0 =
      fullCenteredKernel AES.wordMix +
        zeroMatrix (AESConcrete.DegreeCentering.distinguishedState (0 : AES.Word)) :=
  pointed_step_activity (by rw [AES.word_card]; norm_num)
    AES.wordSuperboxKernel AES.word_superbox_pointed AES.wordMix

abbrev NonzeroWordState := {x : AES.WordState // x ≠ 0}

/-- Literal restriction of P_A G4 P_A from the paper's nonzero domain. -/
def nonzeroWordActivity : NonzeroWordState → NonzeroWordState → ℝ :=
  subkernel 0 (AESConcrete.CenteredWordStepZeros.centeredWordStepBlock 0 0)

theorem nonzeroWordActivity_eq :
    nonzeroWordActivity = subkernel 0 (fullCenteredKernel AES.wordMix) := by
  funext y x
  rw [nonzeroWordActivity, subkernel, word_activity_kernel_eq]
  have hz : AESConcrete.DegreeCentering.distinguishedState (0 : AES.Word) =
      (0 : AES.WordState) := rfl
  simp [subkernel, zeroMatrix, identityKernel, hz, y.property, x.property]

/-- Printed 6.01/Q² bound, with complex arbitrary joint inputs on nonzero states. -/
theorem word_activity_norm :
    ‖kernelOperator (fun y x => (nonzeroWordActivity y x : ℂ))‖ ≤
      (601/100 : ℝ)/wordQ^2 := by
  rw [nonzeroWordActivity_eq]
  exact (subkernel_complex_norm_le_real _ _).trans word_full_norm.le

theorem word_activity_adjoint_norm :
    ‖(kernelOperator (fun y x => (nonzeroWordActivity y x : ℂ))).adjoint‖ ≤
      (601/100 : ℝ)/wordQ^2 := by
  rw [adjoint_norm]
  exact word_activity_norm

/-- Explicit centered activity-vector form of the word-scale comparison. -/
theorem word_activity_centered_energy (f : AES.WordState → ℝ) (hf : f 0 = 0) :
    (∑ y, action (AESConcrete.CenteredWordStepZeros.centeredWordStepBlock 0 0) f y^2) ≤
      ((601/100 : ℝ)/wordQ^2)^2 * ∑ x, f x^2 := by
  rw [word_activity_centered_action f hf]
  exact (real_energy_of_norm _ f).trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (by norm_num [wordQ])).mpr word_full_norm.le)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem word_raw_activity_centered_energy (f : AES.WordState → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, action (AESConcrete.WordStepZeros.wordStepBlock 0 0) f y^2) ≤
      ((601/100 : ℝ)/wordQ^2)^2 * ∑ x, f x^2 := by
  rw [word_raw_activity_centered_action f hz hs]
  rw [← word_activity_centered_action f hz]
  exact word_activity_centered_energy f hz

theorem byte_R00_complex_norm (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (fun y x => (activityBlock (wordKernel left right inverse) y x : ℂ))‖ <
      (63/10 : ℝ)/256^2 :=
  (complex_norm_le_real _).trans_lt (byte_R00_norm left right inverse)

theorem byte_R00_adjoint_norm (left right : Orientation) (inverse : Bool) :
    ‖(kernelOperator (fun y x => (activityBlock (wordKernel left right inverse) y x : ℂ))).adjoint‖ <
      (63/10 : ℝ)/256^2 := by
  rw [adjoint_norm]
  exact byte_R00_complex_norm left right inverse

theorem byte_R00_adjoint_hs (left right : Orientation) (inverse : Bool) :
    wordQ*(AESConcrete.HilbertSchmidtEnergy.hs
      (fun y x => activityBlock (wordKernel left right inverse) x y))^2 < 71 := by
  rw [AESConcrete.HilbertSchmidtEnergy.hs_transpose]
  exact byte_R00_hs_named left right inverse

/-- The printed three constants, with physical operators and full adjoints. -/
theorem printed_activity_bounds (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (activityBlock (wordKernel left right inverse))‖ < (63/10 : ℝ)/256^2 ∧
    wordQ*(AESConcrete.HilbertSchmidtEnergy.hs
      (activityBlock (wordKernel left right inverse)))^2 < 71 ∧
    ‖kernelOperator (fun y x => (nonzeroWordActivity y x : ℂ))‖ ≤ (601/100 : ℝ)/wordQ^2 :=
  ⟨byte_R00_norm left right inverse, byte_R00_hs_named left right inverse, word_activity_norm⟩

end AES8.PaperActivityPhysicalBounds
