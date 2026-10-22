/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ReturnOuterEncoding
import AES8.Reductions.Return.ReturnCrossMiddleActualL2
import AESMixing.L2Sums

/-! Counting-norm composition on the literal projected domains.
The signed input coefficient is restricted, never assumed to have product form.
Frame endpoint scalars remain explicit. These generic bounds do not themselves
close a return cell. Formal-node integration and independent review are separate. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators
namespace AES8.ReturnBranchNorm
open AESMixing AESMixing.AES
open AES8.ProjectedGraph AES8.ZeroOutsideProjection
open AES8.PhysicalZeroPattern (channelTail frameReturnKernel fourReturnKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

theorem subtype_l2_le {X : Type*} [Fintype X] (p : X → Prop)
    [DecidablePred p] (f : X → ℝ) :
    l2 (fun x : {x // p x} => f x.val) ≤ l2 f := by
  apply (sq_le_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  simp only [l2_sq]
  rw [← indicator_weight_subtype p (fun x => f x ^ 2)]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : p x
  · simp only [h, if_true, _root_.one_mul, le_refl]
  · simp only [h, if_false, zero_mul]
    exact sq_nonneg _

theorem input_l2_le (c z : Fin 4) (t : Bool) (f : WordState → ℝ) :
    l2 (fun x : RightDomain c z t => inputCoefficient z f x.val) ≤ l2 (Q z f) := by
  have he : (fun x : RightDomain c z t => inputCoefficient z f x.val) =
      (fun x : RightDomain c z t => Q z f x.val) := by
    funext x
    rw [Q_apply, if_pos x.property.1]
  rw [he]
  exact subtype_l2_le (RightConstraint c z t) (Q z f)

theorem hyperplane_input_l2_le (z : Fin 4) (f : WordState → ℝ) :
    l2 (fun x : RightHyperplane z => inputCoefficient z f x.val) ≤ l2 (Q z f) := by
  have he : (fun x : RightHyperplane z => inputCoefficient z f x.val) =
      (fun x : RightHyperplane z => Q z f x.val) := by
    funext x
    rw [Q_apply, if_pos x.property]
  rw [he]
  exact subtype_l2_le (fun x : WordState => x z = 0) (Q z f)

theorem embed_l2 (r : Fin 4) (g : (OutsideCoordinates r → AES.Word) → ℝ) :
    l2 (embedZero r g) = l2 g := by
  apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  simp only [l2_sq, embedZero_energy]

theorem frame_l2_of_bounds (r c z : Fin 4) (s t : Bool) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (houter : ∀ g : LeftDomain r c s → ℝ,
      l2 (action (ReturnOuterEncoding.actualKernel s) g) ≤ A * l2 g)
    (hmiddle : ∀ g : RightDomain c z t → ℝ,
      l2 (fun v : LeftDomain r c s => ∑ x : RightDomain c z t,
        channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * g x) ≤ B * l2 g)
    (f : WordState → ℝ) :
    l2 (Q r (action (frameReturnKernel c s t) (Q z f))) ≤
      (|frameScalar s * frameScalar t| * (A * B)) * l2 (Q z f) := by
  rw [ReturnOuterEncoding.projected_frame_eq_embed_outer, embed_l2, l2_scale]
  have hm := hmiddle (fun x => inputCoefficient z f x.val)
  have ho := houter (fun v => ∑ x : RightDomain c z t,
    channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * inputCoefficient z f x.val)
  calc
    _ ≤ |frameScalar s * frameScalar t| *
        (A * l2 (fun v : LeftDomain r c s => ∑ x : RightDomain c z t,
          channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * inputCoefficient z f x.val)) :=
      mul_le_mul_of_nonneg_left ho (abs_nonneg _)
    _ ≤ |frameScalar s * frameScalar t| *
        (A * (B * l2 (fun x : RightDomain c z t => inputCoefficient z f x.val))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hA) (abs_nonneg _)
    _ ≤ |frameScalar s * frameScalar t| * (A * (B * l2 (Q z f))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (input_l2_le c z t f) hB) hA) (abs_nonneg _)
    _ = _ := by ring

theorem four_l2_of_middle (r z : Fin 4) (B : ℝ) (hB : 0 ≤ B)
    (hmiddle : ∀ g : RightHyperplane z → ℝ,
      l2 (fun v : LeftHyperplane r => ∑ x : RightHyperplane z,
        AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) * g x) ≤ B * l2 g)
    (f : WordState → ℝ) :
    l2 (Q r (action fourReturnKernel (Q z f))) ≤
      (SharpWordNorm.rho ^ 3 * B) * l2 (Q z f) := by
  rw [ReturnOuterEncoding.projected_four_eq_embed_outer, embed_l2]
  have hm := hmiddle (fun x => inputCoefficient z f x.val)
  have ho := ReturnOuterEncoding.actual_hyperplane_l2 r
    (fun v => ∑ x : RightHyperplane z,
      AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) * inputCoefficient z f x.val)
  have hr : 0 ≤ SharpWordNorm.rho ^ 3 := by norm_num [SharpWordNorm.rho]
  calc
    _ ≤ SharpWordNorm.rho ^ 3 * l2 (fun v : LeftHyperplane r => ∑ x : RightHyperplane z,
      AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) * inputCoefficient z f x.val) := ho
    _ ≤ SharpWordNorm.rho ^ 3 * (B * l2 (fun x : RightHyperplane z => inputCoefficient z f x.val)) :=
      mul_le_mul_of_nonneg_left hm hr
    _ ≤ SharpWordNorm.rho ^ 3 * (B * l2 (Q z f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hyperplane_input_l2_le z f) hB) hr
    _ = _ := by ring

end AES8.ReturnBranchNorm
