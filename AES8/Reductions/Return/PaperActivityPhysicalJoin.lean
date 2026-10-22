import AES8.Math.PaperActivityFullCompression
import AES8.Math.PaperFiberKernel
import AESConcrete.ActivityTrace
import AESConcrete.CenteredWordStepZeros
import AESMixing.ByteResidualConcrete

/-! Physical joins for the printed activity calculation, paper1906c42.
The byte residual removes both fixed directions. The grouped word step removes
only the uniform nonzero direction; its extra zero-state projection is retained
until restriction to inputs vanishing at zero. Constructive proofs only; no
attacks, manuscript/vendor changes, or claimed closure of the full theorem. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityPhysicalJoin
open AESMixing PaperKernelBounds PaperActivityFullCompression
open AESConcrete.WordChannelCommutation
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_left compose_sub_right)
open AESConcrete.DegreeCentering (distinguishedState globalUniformKernel)
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem coordinate_degree_zero_right (D : V → V → ℝ)
    (hD : PointedBistochastic D 0) :
    kernelCompose (coordinateKernel (fun _ : Fin 4 => D)) (degreeKernel (0 : V) 0) =
      degreeKernel 0 0 := by
  rw [degreeKernel_zero]
  change kernelCompose (coordinateKernel (fun _ : Fin 4 => D))
    (coordinateKernel (fun _ : Fin 4 => activityMatrix (0 : V))) = _
  rw [coordinateKernel_compose]
  congr 1
  funext i
  exact pointed_activity_right hD

theorem pointed_transpose (D : V → V → ℝ) (hD : PointedBistochastic D 0) :
    PointedBistochastic (fun y x => D x y) 0 :=
  ⟨fun y x => hD.nonnegative x y, hD.zero_column, hD.zero_row,
    hD.row_sum, hD.column_sum⟩

/-- Both the substitution and its counting-measure adjoint fix activity. -/
theorem coordinate_adjoint_activity (D : V → V → ℝ) (hD : PointedBistochastic D 0) :
    kernelCompose (degreeKernel (0 : V) 0)
      (coordinateKernel (fun _ : Fin 4 => fun y x => D x y)) = degreeKernel 0 0 ∧
    kernelCompose (coordinateKernel (fun _ : Fin 4 => fun y x => D x y))
      (degreeKernel (0 : V) 0) = degreeKernel 0 0 :=
  ⟨coordinate_degree_zero_left (fun _ : Fin 4 => pointed_transpose D hD),
    coordinate_degree_zero_right _ (pointed_transpose D hD)⟩

/-- Two actual tensor substitutions around a zero-preserving diffusion. -/
def twoTensorKernel (D E : V → V → ℝ) (L : (Fin 4 → V) ≃+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (coordinateKernel (fun _ : Fin 4 => D))
    (fun y x => coordinateKernel (fun _ : Fin 4 => E) (L.symm y) x)

theorem raw_two_tensor_activity (D E : V → V → ℝ)
    (hD : PointedBistochastic D 0) (hE : PointedBistochastic E 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) :
    kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose (twoTensorKernel D E L) (degreeKernel 0 0)) =
      kernelCompose (fun y z => degreeKernel (0 : V) 0 y (L z)) (degreeKernel 0 0) := by
  have hright : kernelCompose
      (fun y x => coordinateKernel (fun _ : Fin 4 => E) (L.symm y) x)
      (degreeKernel (0 : V) 0) = fun y x => degreeKernel (0 : V) 0 (L.symm y) x := by
    funext y x
    exact congrFun (congrFun (coordinate_degree_zero_right E hE) (L.symm y)) x
  have hleft := coordinate_degree_zero_left (fun _ : Fin 4 => hD)
  calc
    _ = kernelCompose (degreeKernel (0 : V) 0)
        (kernelCompose (coordinateKernel (fun _ : Fin 4 => D))
          (fun y x => degreeKernel (0 : V) 0 (L.symm y) x)) := by
      rw [twoTensorKernel, ← compose_assoc, hright]
    _ = kernelCompose (degreeKernel (0 : V) 0)
        (fun y x => degreeKernel (0 : V) 0 (L.symm y) x) := by
      rw [compose_assoc, hleft]
    _ = _ := by
      funext y x
      change (∑ z, degreeKernel (0 : V) 0 y z * degreeKernel (0 : V) 0 (L.symm z) x) = _
      rw [← L.toEquiv.sum_comp (fun z =>
        degreeKernel (0 : V) 0 y z * degreeKernel (0 : V) 0 (L.symm z) x)]
      simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, L.symm_apply_apply]
      rfl

theorem global_fixed_split :
    activityMatrix (0 : Fin 4 → V) =
      zeroMatrix (distinguishedState (0 : V)) + globalUniformKernel 0 := by
  funext y x
  have hz : distinguishedState (0 : V) = (0 : Fin 4 → V) := rfl
  by_cases hy : y = 0 <;> by_cases hx : x = 0 <;>
    simp [activityMatrix, zeroMatrix, identityKernel, globalUniformKernel, hz, hy, hx]

theorem sandwich_fixed (hn : 1 < Fintype.card V) :
    kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose (activityMatrix (0 : Fin 4 → V)) (degreeKernel (0 : V) 0)) =
      activityMatrix (0 : Fin 4 → V) := by
  have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
    degree_zero_pointed (0 : V) hn
  rw [pointed_activity_left (z := (0 : Fin 4 → V)) hp,
    pointed_activity_right (z := (0 : Fin 4 → V)) hp]

/-- Exact kernel equality, before any norm comparison or scalar rounding. -/
theorem two_tensor_residual_activity (hn : 1 < Fintype.card V)
    (D E : V → V → ℝ) (hD : PointedBistochastic D 0) (hE : PointedBistochastic E 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) :
    kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose (residualMatrix (twoTensorKernel D E L) 0) (degreeKernel 0 0)) =
      fullCenteredKernel L.toAddMonoidHom := by
  change kernelCompose (degreeKernel (0 : V) 0)
    (kernelCompose (twoTensorKernel D E L - activityMatrix (0 : Fin 4 → V))
      (degreeKernel 0 0)) = _
  rw [compose_sub_left, compose_sub_right, raw_two_tensor_activity D E hD hE L,
    sandwich_fixed hn, global_fixed_split]
  rfl

/-- The printed byte-scale R00, for all actual channel orientations and both
diffusion directions, is the literal frozen full centered MDS kernel. -/
theorem byte_R00_eq (left right : AESConcrete.ByteOrientations.Orientation) (inverse : Bool) :
    AESConcrete.ActivityTrace.activityBlock
      (AESConcrete.WordOrientationClosure.wordKernel left right inverse) =
      fullCenteredKernel (byteDiffusionOrientedAddEquiv inverse).toAddMonoidHom := by
  change kernelCompose (kernelCompose (degreeKernel (0 : BinaryWord 8) 0)
    (residualMatrix (AESConcrete.WordOrientationClosure.wordKernel left right inverse) 0))
      (degreeKernel 0 0) = _
  rw [← compose_assoc]
  have ht : AESConcrete.WordOrientationClosure.wordKernel left right inverse =
      twoTensorKernel (AESConcrete.ByteOrientations.channel left)
        (AESConcrete.ByteOrientations.channel right) (byteDiffusionOrientedAddEquiv inverse) := by
    simp only [AESConcrete.WordOrientationClosure.wordKernel, twoSubstitutionKernel,
      twoTensorKernel, substitutionKernel]
    cases inverse <;> rfl
  rw [ht]
  exact two_tensor_residual_activity (by norm_num [BinaryWord.card]) _ _
    (AESConcrete.ByteOrientations.channel_resources left).pointed
    (AESConcrete.ByteOrientations.channel_resources right).pointed _

theorem zero_state_action (f : (Fin 4 → V) → ℝ) (hf : f 0 = 0) :
    action (zeroMatrix (distinguishedState (0 : V))) f = 0 := by
  change action (zeroMatrix (0 : Fin 4 → V)) f = 0
  funext y
  simp [action, zeroMatrix, identityKernel, hf]

/-- A centered grouped step retains its fixed zero state on the full space.
This identity records the extra projection instead of silently discarding it. -/
theorem pointed_step_activity (hn : 1 < Fintype.card V)
    (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (degreeKernel 0 0)) =
      fullCenteredKernel L + zeroMatrix (distinguishedState (0 : V)) := by
  have hleft : kernelCompose (degreeKernel (0 : V) 0)
      (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) =
      fun y x => degreeKernel (0 : V) 0 y (L x) := by
    funext y x
    exact congrFun (congrFun
      (coordinate_degree_zero_left (fun _ : Fin 4 => hD)) y) (L x)
  have hglobal : kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose (globalUniformKernel 0) (degreeKernel (0 : V) 0)) =
      globalUniformKernel 0 := by
    have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
      degree_zero_pointed (0 : V) hn
    have hz : distinguishedState (0 : V) = (0 : Fin 4 → V) := rfl
    have hzleft : kernelCompose (degreeKernel (0 : V) 0)
        (zeroMatrix (distinguishedState (0 : V))) = zeroMatrix (distinguishedState (0 : V)) := by
      funext y x
      by_cases hx : x = 0
      · simpa [kernelCompose, zeroMatrix, identityKernel, hz, hx] using hp.zero_column y
      · simp [kernelCompose, zeroMatrix, identityKernel, hz, hx]
    have hzright : kernelCompose (zeroMatrix (distinguishedState (0 : V)))
        (degreeKernel (0 : V) 0) = zeroMatrix (distinguishedState (0 : V)) := by
      funext y x
      by_cases hy : y = 0
      · simpa [kernelCompose, zeroMatrix, identityKernel, hz, hy] using hp.zero_row x
      · simp [kernelCompose, zeroMatrix, identityKernel, hz, hy]
    have hq : globalUniformKernel (0 : V) =
        activityMatrix (0 : Fin 4 → V) - zeroMatrix (distinguishedState (0 : V)) := by
      funext y x
      have he := congrFun (congrFun (global_fixed_split (V := V)) y) x
      simp only [Pi.add_apply] at he
      simp only [Pi.sub_apply]
      linarith
    rw [hq, compose_sub_left, compose_sub_right,
      pointed_activity_left (z := (0 : Fin 4 → V)) hp,
      pointed_activity_right (z := (0 : Fin 4 → V)) hp, hzright, hzleft]
  rw [compose_sub_left, compose_sub_right, compose_assoc, hleft]
  rw [hglobal]
  funext y x
  simp only [fullCenteredKernel, Pi.sub_apply, Pi.add_apply]
  ring

theorem pointed_step_centered_action (hn : 1 < Fintype.card V)
    (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : (Fin 4 → V) →+ (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) (hf : f 0 = 0) :
    action (kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (degreeKernel 0 0))) f = action (fullCenteredKernel L) f := by
  rw [pointed_step_activity hn D hD L, kernel_action_add, zero_state_action f hf]
  simp

theorem word_activity_centered_action (f : AES.WordState → ℝ) (hf : f 0 = 0) :
    action (AESConcrete.CenteredWordStepZeros.centeredWordStepBlock 0 0) f =
      action (fullCenteredKernel AES.wordMix) f :=
  pointed_step_centered_action (by rw [AES.word_card]; norm_num)
    AES.wordSuperboxKernel AES.word_superbox_pointed AES.wordMix f hf

/-- On globally centered inputs the literal uncentered grouped sandwich has
the same action. Both zero-value and total-mass hypotheses are explicit. -/
theorem raw_pointed_activity_centered_action (hn : 1 < Fintype.card V)
    (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : (Fin 4 → V) →+ (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (kernelCompose (degreeKernel (0 : V) 0)
      (kernelCompose (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x))
        (degreeKernel 0 0))) f = action (fullCenteredKernel L) f := by
  have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
    degree_zero_pointed (0 : V) hn
  have hzero : action (degreeKernel (0 : V) 0) f (distinguishedState (0 : V)) = 0 :=
    (hp.action_zero f).trans hz
  have hsum : (∑ x, action (degreeKernel (0 : V) 0) f x) = 0 :=
    (hp.action_sum f).trans hs
  have hU := AESConcrete.DegreeCentering.globalUniformKernel_action_eq_zero
    (0 : V) (action (degreeKernel (0 : V) 0) f) hzero hsum
  have h := pointed_step_centered_action hn D hD L f hz
  simpa only [kernelCompose_action, kernel_action_sub, hU, sub_zero] using h

theorem word_raw_activity_centered_action (f : AES.WordState → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (AESConcrete.WordStepZeros.wordStepBlock 0 0) f =
      action (fullCenteredKernel AES.wordMix) f :=
  raw_pointed_activity_centered_action (by rw [AES.word_card]; norm_num)
    AES.wordSuperboxKernel AES.word_superbox_pointed AES.wordMix f hz hs

end AES8.PaperActivityPhysicalJoin
