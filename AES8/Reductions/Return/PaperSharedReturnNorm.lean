import AES8.Math.PaperKernelLinear
import AES8.Reductions.Return.PhysicalZeroPattern

/-! The shared middle metric contributes once to the physical high return.
Arbitrary outside operators are retained. Exact signed expansion precedes the
norm inequality; its branch bounds remain explicit for subsequent graph joins. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSharedReturnNorm
open AESMixing AESMixing.AES PaperKernelBounds PaperKernelLinear
open PhysicalZeroPattern WordActivityFrame
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

abbrev FrameLabel := Fin 4 × Bool × Bool
def weight (i : FrameLabel) : ℝ := wordInverse AES.Word i.2.1 i.2.2
def branch (i : FrameLabel) : WordState → WordState → ℝ :=
  frameReturnKernel i.1 i.2.1 i.2.2

theorem operator_expansion :
    kernelOperator ReturnCentering.physicalReturnKernel =
      (∑ i : FrameLabel, weight i • kernelOperator (branch i)) +
        kernelOperator fourReturnKernel := by
  have he : ReturnCentering.physicalReturnKernel = fun y x =>
      (∑ i : FrameLabel, weight i * branch i y x) + fourReturnKernel y x := by
    funext y x
    simpa only [Fintype.sum_prod_type, weight, branch] using
      physicalReturnKernel_frame_expansion y x
  rw [he, operator_add, operator_sum]
  simp_rw [operator_smul]

theorem eta_nonneg : 0 ≤ eta AES.Word := by
  have h := q_gt_one AESConcrete.AES.word_card_gt_one
  exact div_nonneg (by unfold q; positivity) (by linarith)

theorem xi_nonneg : 0 ≤ xi AES.Word := by unfold xi; positivity

theorem abs_weight (i : FrameLabel) :
    |weight i| = eta AES.Word * if i.2.1 = i.2.2 then 1 else xi AES.Word := by
  rw [weight, wordInverse, abs_mul, abs_of_nonneg eta_nonneg]
  split_ifs <;> simp only [abs_one, abs_neg, abs_of_nonneg xi_nonneg]

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem outside_expansion
    (A : EuclideanSpace ℝ WordState →L[ℝ] EuclideanSpace ℝ Y)
    (B : EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ WordState) :
    A.comp ((kernelOperator ReturnCentering.physicalReturnKernel).comp B) =
      (∑ i : FrameLabel, weight i • A.comp ((kernelOperator (branch i)).comp B)) +
        A.comp ((kernelOperator fourReturnKernel).comp B) := by
  rw [operator_expansion]
  ext f y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_add, map_sum,
    map_smul, WithLp.ofLp_sum, WithLp.ofLp_add, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply]

/-- Arbitrary physical outside operators; every actual middle branch is
bounded before the shared signed weights are replaced by absolute values. -/
theorem outside_norm
    (A : EuclideanSpace ℝ WordState →L[ℝ] EuclideanSpace ℝ Y)
    (B : EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ WordState)
    (g : Bool → Bool → ℝ) (g4 : ℝ)
    (h3 : ∀ i : FrameLabel,
      ‖A.comp ((kernelOperator (branch i)).comp B)‖ ≤ g i.2.1 i.2.2)
    (h4 : ‖A.comp ((kernelOperator fourReturnKernel).comp B)‖ ≤ g4) :
    ‖A.comp ((kernelOperator ReturnCentering.physicalReturnKernel).comp B)‖ ≤
      4 * eta AES.Word *
        (g false false + xi AES.Word * g false true +
          xi AES.Word * g true false + g true true) + g4 := by
  rw [outside_expansion]
  calc
    _ ≤ ‖∑ i : FrameLabel, weight i • A.comp ((kernelOperator (branch i)).comp B)‖ +
        ‖A.comp ((kernelOperator fourReturnKernel).comp B)‖ := norm_add_le _ _
    _ ≤ (∑ i : FrameLabel, ‖weight i • A.comp ((kernelOperator (branch i)).comp B)‖) + g4 :=
      add_le_add (norm_sum_le _ _) h4
    _ = (∑ i : FrameLabel, |weight i| * ‖A.comp ((kernelOperator (branch i)).comp B)‖) + g4 := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (∑ i : FrameLabel, |weight i| * g i.2.1 i.2.2) + g4 := by
      exact add_le_add (Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (h3 i) (abs_nonneg _))) le_rfl
    _ = _ := by
      simp only [abs_weight, Fintype.sum_prod_type, Fintype.sum_bool,
        Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, _root_.mul_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring

end AES8.PaperSharedReturnNorm
