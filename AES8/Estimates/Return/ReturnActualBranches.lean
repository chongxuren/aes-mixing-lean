/- Module role: Selected concrete high-return estimates.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ReturnBranchNorm
import AES8.Reductions.Return.ReturnMiddleDomainBridges
import AES8.Historical.ReturnElevenScalar

/-! Actual projected branch bounds, with the two endpoint scalars retained.
The slightly larger rational nu is used only after the proved rho bounds. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators
namespace AES8.ReturnActualBranches
open AESMixing AESMixing.AES
open AES8.ProjectedGraph AES8.ZeroOutsideProjection
open AES8.PhysicalZeroPattern (channelTail frameReturnKernel fourReturnKernel)
open AES8.ReturnElevenScalar (delta nu xi eta)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

def beta (s t : Bool) : ℝ := match s, t with
  | false, false => nu ^ 3 * delta * Real.sqrt delta
  | false, true => xi * nu ^ 5 * Real.sqrt delta
  | true, false => xi * nu ^ 5 * Real.sqrt delta
  | true, true => xi ^ 2 * nu ^ 6

def betaFour : ℝ := delta * nu ^ 5
def outerCap (s : Bool) : ℝ := if s then nu ^ 3 else nu ^ 2 * Real.sqrt delta
def middleCap (s t : Bool) : ℝ := match s, t with
  | false, false => delta * nu
  | false, true => nu ^ 3
  | true, false => nu ^ 2 * Real.sqrt delta
  | true, true => nu ^ 3

theorem delta_nonneg : 0 ≤ delta := by norm_num [delta, ReturnElevenScalar.q]
theorem nu_nonneg : 0 ≤ nu := by norm_num [nu]
theorem xi_nonneg : 0 ≤ xi := by norm_num [xi]
theorem columnCap_eq : OneSourceEventMoment.columnCap = delta := by
  norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q, delta, ReturnElevenScalar.q]
theorem rho_le_nu : SharpWordNorm.rho ≤ nu := by norm_num [SharpWordNorm.rho, nu]

theorem word_xi_eq : WordActivityFrame.xi AES.Word = xi := by
  have hq : WordActivityFrame.q AES.Word = (65536 : ℝ) ^ 2 := by
    norm_num [WordActivityFrame.q, AES.Word, BinaryWord.card, Fintype.card_fun]
  rw [WordActivityFrame.xi, hq, Real.sqrt_sq_eq_abs]
  norm_num [xi]

theorem word_eta_eq : WordActivityFrame.eta AES.Word = eta := by
  norm_num [WordActivityFrame.eta, WordActivityFrame.q, AES.Word, BinaryWord.card,
    Fintype.card_fun, eta, ReturnElevenScalar.q]

theorem outerCap_nonneg (s : Bool) : 0 ≤ outerCap s := by
  cases s <;> simp only [outerCap, Bool.false_eq_true, if_false, if_true]
  · exact mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  · exact pow_nonneg nu_nonneg _

theorem middleCap_nonneg (s t : Bool) : 0 ≤ middleCap s t := by
  cases s <;> cases t <;> simp only [middleCap]
  · exact mul_nonneg delta_nonneg nu_nonneg
  · exact pow_nonneg nu_nonneg _
  · exact mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  · exact pow_nonneg nu_nonneg _

theorem actual_outer_le (r c : Fin 4) (s : Bool) (f : LeftDomain r c s → ℝ) :
    l2 (action (ReturnOuterEncoding.actualKernel s) f) ≤ outerCap s * l2 f := by
  cases s
  · have h := ReturnOuterEncoding.actual_false_l2 r c f
    rw [columnCap_eq] at h
    apply h.trans
    change (SharpWordNorm.rho ^ 2 * Real.sqrt delta) * l2 f ≤
      (nu ^ 2 * Real.sqrt delta) * l2 f
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num [SharpWordNorm.rho]) rho_le_nu 2)
        (Real.sqrt_nonneg _)) (l2_nonneg _)
  · have h := ReturnOuterEncoding.actual_true_l2 r c f
    apply h.trans
    change SharpWordNorm.rho ^ 3 * l2 f ≤ nu ^ 3 * l2 f
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num [SharpWordNorm.rho]) rho_le_nu 3) (l2_nonneg _)

theorem cross_action_eq (r c z : Fin 4) (s t : Bool) (f : RightDomain c z t → ℝ) :
    (fun v : LeftDomain r c s => ∑ x : RightDomain c z t,
      channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * f x) =
      action (ReturnCrossMiddle.actualKernel r c z s t) f := by
  funext v
  unfold AESMixing.action
  apply Finset.sum_congr rfl
  intro x _
  rw [ReturnCrossMiddle.actualKernel_eq_channelTail]

theorem actual_middle_le (r c z : Fin 4) (s t : Bool) (f : RightDomain c z t → ℝ) :
    l2 (fun v : LeftDomain r c s => ∑ x : RightDomain c z t,
      channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * f x) ≤
        middleCap s t * l2 f := by
  cases s <;> cases t
  · have he : (fun v : LeftDomain r c false => ∑ x : RightDomain c z false,
        channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * f x) =
        action (ReturnMiddleDomainBridges.zeroKernel r c z) f := by
      funext v
      unfold AESMixing.action
      apply Finset.sum_congr rfl
      intro x _
      rw [ReturnMiddleDomainBridges.zeroKernel_eq_channelTail]
    rw [he]
    have h := ReturnMiddleDomainBridges.actual_zero_l2 r c z f
    rw [columnCap_eq] at h
    apply h.trans
    change (delta * SharpWordNorm.rho) * l2 f ≤ (delta * nu) * l2 f
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left rho_le_nu delta_nonneg) (l2_nonneg _)
  · rw [cross_action_eq]
    apply (ReturnCrossMiddleActualL2.actual_zero_one_l2 r c z f).trans
    change SharpWordNorm.rho ^ 3 * l2 f ≤ nu ^ 3 * l2 f
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num [SharpWordNorm.rho]) rho_le_nu 3) (l2_nonneg _)
  · rw [cross_action_eq]
    have h := ReturnCrossMiddleActualL2.actual_one_zero_l2 r c z
      (ReturnOuterEncoding.outsideSplit c) f
    rw [columnCap_eq] at h
    apply h.trans
    change (SharpWordNorm.rho ^ 2 * Real.sqrt delta) * l2 f ≤
      (nu ^ 2 * Real.sqrt delta) * l2 f
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num [SharpWordNorm.rho]) rho_le_nu 2)
        (Real.sqrt_nonneg _)) (l2_nonneg _)
  · rw [cross_action_eq]
    apply (ReturnCrossMiddleActualL2.actual_eleven_l2 r c z f).trans
    change SharpWordNorm.rho ^ 3 * l2 f ≤ nu ^ 3 * l2 f
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num [SharpWordNorm.rho]) rho_le_nu 3) (l2_nonneg _)

theorem beta_eq (s t : Bool) :
    |frameScalar s * frameScalar t| * (outerCap s * middleCap s t) = beta s t := by
  have hx := xi_nonneg
  cases s <;> cases t <;>
    simp only [frameScalar, Bool.false_eq_true, if_false, if_true,
      word_xi_eq, outerCap, middleCap, beta, _root_.one_mul, _root_.mul_one]
  all_goals rw [abs_of_nonneg (by positivity)]
  all_goals ring

theorem frame_l2 (r c z : Fin 4) (s t : Bool) (f : WordState → ℝ) :
    l2 (Q r (action (frameReturnKernel c s t) (Q z f))) ≤ beta s t * l2 (Q z f) := by
  have h := ReturnBranchNorm.frame_l2_of_bounds r c z s t (outerCap s) (middleCap s t)
    (outerCap_nonneg s) (middleCap_nonneg s t)
    (actual_outer_le r c s) (actual_middle_le r c z s t) f
  rw [beta_eq] at h
  exact h

theorem four_l2 (r z : Fin 4) (f : WordState → ℝ) :
    l2 (Q r (action fourReturnKernel (Q z f))) ≤ betaFour * l2 (Q z f) := by
  have hm (g : RightHyperplane z → ℝ) :
      l2 (fun v : LeftHyperplane r => ∑ x : RightHyperplane z,
        AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) * g x) ≤
          (delta * SharpWordNorm.rho ^ 2) * l2 g := by
    change l2 (action (ReturnMiddleDomainBridges.fourKernel r z) g) ≤ _
    rw [← columnCap_eq]
    exact ReturnMiddleDomainBridges.actual_four_l2 r z g
  have hr : 0 ≤ SharpWordNorm.rho := by norm_num [SharpWordNorm.rho]
  have h := ReturnBranchNorm.four_l2_of_middle r z (delta * SharpWordNorm.rho ^ 2)
    (mul_nonneg delta_nonneg (sq_nonneg _)) hm f
  apply h.trans
  have he : SharpWordNorm.rho ^ 3 * (delta * SharpWordNorm.rho ^ 2) =
      delta * SharpWordNorm.rho ^ 5 := by ring
  rw [he]
  unfold betaFour
  apply mul_le_mul_of_nonneg_right _ (l2_nonneg _)
  apply mul_le_mul_of_nonneg_left _ delta_nonneg
  exact pow_le_pow_left₀ hr rho_le_nu 5

end AES8.ReturnActualBranches
