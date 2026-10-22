/- Module role: Selected concrete high-return estimates.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Return.ReturnActualBranches
import AES8.Estimates.Return.ReturnElevenBlocks
import AES8.Historical.ReturnElevenScalar

/-!
# Assemble the actual return (11,11)

The exact physical kernel expansion retains one shared signed wordInverse
coefficient on every frame branch. Only after the projected action identity
is established do the norm triangle inequalities replace those coefficients
by their absolute values. The actual branch theorems apply to every signed
joint input. The four-by-four outside-pattern lemma supplies factor four;
the existing scalar margin then fits the exact physical recurrence allowance.

No active-source/root/Audit/RemainingCaps or manuscript/predecessor edits.
Constructive proofs only; no attacks. No claim about other return cells or
the full AES theorem is made by this module.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators

namespace AES8.ReturnEleven
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection
open AES8.PhysicalZeroPattern (frameReturnKernel fourReturnKernel)
open AES8.ReturnElevenScalar (assembled delta nu xi eta)
open AES8.ReturnActualBranches (beta betaFour)
open AES8.SupportProfile (component profile)

/-- The actual word alphabet has q=2^32; no AES state is enumerated. -/
theorem word_q_eq : WordActivityFrame.q AES.Word = ReturnElevenScalar.q := by
  norm_num [WordActivityFrame.q, AES.Word, BinaryWord.card, Fintype.card_fun,
    ReturnElevenScalar.q]

theorem word_xi_eq : WordActivityFrame.xi AES.Word = xi := by
  have hs : Real.sqrt (WordActivityFrame.q AES.Word) = 65536 := by
    rw [word_q_eq, show ReturnElevenScalar.q = (65536 : ℝ) ^ 2 by
      norm_num [ReturnElevenScalar.q], Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
  rw [WordActivityFrame.xi, hs]
  rfl

theorem word_eta_eq : WordActivityFrame.eta AES.Word = eta := by
  rw [WordActivityFrame.eta, word_q_eq]
  rfl

private theorem eta_nonneg : 0 ≤ eta := by
  norm_num [ReturnElevenScalar.eta, ReturnElevenScalar.q]

private theorem xi_nonneg : 0 ≤ xi := by norm_num [ReturnElevenScalar.xi]

/-- Both negative off-diagonal coefficients remain in this exact identity. -/
theorem inverse_eq (s t : Bool) :
    WordActivityFrame.wordInverse AES.Word s t =
      eta * if s = t then 1 else -xi := by
  rw [WordActivityFrame.wordInverse, word_eta_eq, word_xi_eq]

theorem abs_inverse_eq (s t : Bool) :
    |WordActivityFrame.wordInverse AES.Word s t| =
      eta * if s = t then 1 else xi := by
  rw [inverse_eq, abs_mul, abs_of_nonneg eta_nonneg]
  by_cases h : s = t
  · simp only [h, if_true, abs_one]
  · simp only [h, if_false, abs_neg, abs_of_nonneg xi_nonneg]

abbrev FrameLabel := Fin 4 × Bool × Bool

def frameWeight (i : FrameLabel) : ℝ :=
  WordActivityFrame.wordInverse AES.Word i.2.1 i.2.2

def frameKernel (i : FrameLabel) : WordState → WordState → ℝ :=
  frameReturnKernel i.1 i.2.1 i.2.2

/-- This finite sum has all four omissions and all four signed metric entries. -/
theorem physical_kernel_expansion (y x : WordState) :
    ReturnCentering.physicalReturnKernel y x =
      (∑ i : FrameLabel, frameWeight i * frameKernel i y x) + fourReturnKernel y x := by
  simpa only [Fintype.sum_prod_type, frameWeight, frameKernel] using
    PhysicalZeroPattern.physicalReturnKernel_frame_expansion y x

private theorem action_scale_input {A B : Type*} [Fintype B]
    (K : A → B → ℝ) (a : ℝ) (g : B → ℝ) :
    action K (fun x => a * g x) = fun y => a * action K g y := by
  funext y
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem action_add_input {A B : Type*} [Fintype B]
    (K : A → B → ℝ) (g h : B → ℝ) :
    action K (g + h) = action K g + action K h := by
  funext y
  simp only [action, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem Q_scale_input (r : Fin 4) (a : ℝ) (g : WordState → ℝ) :
    Q r (fun x => a * g x) = fun y => a * Q r g y := by
  simp only [Q_eq_support_action, action_scale_input]

private theorem Q_add_input (r : Fin 4) (g h : WordState → ℝ) :
    Q r (g + h) = Q r g + Q r h := by
  simp only [Q_eq_support_action, action_add_input]

private theorem Q_weighted_sum {I : Type*} [Fintype I]
    (r : Fin 4) (a : I → ℝ) (g : I → WordState → ℝ) :
    Q r (fun x => ∑ i, a i * g i x) = fun y => ∑ i, a i * Q r (g i) y := by
  rw [ReturnElevenBlocks.Q_sum]
  funext y
  apply Finset.sum_congr rfl
  intro i _
  rw [Q_scale_input]

/-- The exact kernel equality is distributed before any norm estimate. -/
theorem physical_action_expansion (f : WordState → ℝ) :
    action ReturnCentering.physicalReturnKernel f =
      (fun y => ∑ i : FrameLabel, frameWeight i * action (frameKernel i) f y) +
        action fourReturnKernel f := by
  funext y
  simp only [action, Pi.add_apply]
  simp_rw [physical_kernel_expansion]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  apply congrArg (fun a : ℝ => a + ∑ x, fourReturnKernel y x * f x)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- All signed metric weights remain literal through both outside projections. -/
theorem projected_block_expansion (r z : Fin 4) (f : WordState → ℝ) :
    Q r (action ReturnCentering.physicalReturnKernel (Q z f)) =
      (fun y => ∑ i : FrameLabel,
        frameWeight i * Q r (action (frameKernel i) (Q z f)) y) +
        Q r (action fourReturnKernel (Q z f)) := by
  rw [physical_action_expansion, Q_add_input, Q_weighted_sum]

private theorem bool_weighted_beta_sum :
    (∑ s : Bool, ∑ t : Bool, |WordActivityFrame.wordInverse AES.Word s t| * beta s t) =
      eta * (nu ^ 3 * delta * Real.sqrt delta +
        2 * xi ^ 2 * nu ^ 5 * Real.sqrt delta + xi ^ 2 * nu ^ 6) := by
  simp only [Fintype.sum_bool, abs_inverse_eq, ReturnActualBranches.beta,
    Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, _root_.mul_one]
  ring

/-- Four degree-three omissions and one four-middle term give assembled/4 per block. -/
theorem weighted_beta_sum :
    (∑ i : FrameLabel, |frameWeight i| * beta i.2.1 i.2.2) + betaFour = assembled / 4 := by
  simp only [Fintype.sum_prod_type, frameWeight, bool_weighted_beta_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  unfold ReturnActualBranches.betaFour ReturnElevenScalar.assembled
  ring

theorem assembled_nonneg : 0 ≤ assembled := by
  unfold ReturnElevenScalar.assembled
  have hd : 0 ≤ delta := by norm_num [ReturnElevenScalar.delta, ReturnElevenScalar.q]
  have hn : 0 ≤ nu := by norm_num [ReturnElevenScalar.nu]
  have he := eta_nonneg
  have hx := xi_nonneg
  positivity

/-- Actual uniform block bound, after the triangle inequality with absolute weights. -/
theorem physical_block_l2 (r z : Fin 4) (f : WordState → ℝ) :
    l2 (Q r (action ReturnCentering.physicalReturnKernel (Q z f))) ≤
      (assembled / 4) * l2 (Q z f) := by
  rw [projected_block_expansion]
  calc
    _ ≤ l2 (fun y => ∑ i : FrameLabel,
          frameWeight i * Q r (action (frameKernel i) (Q z f)) y) +
        l2 (Q r (action fourReturnKernel (Q z f))) := l2_add_le _ _
    _ ≤ (∑ i : FrameLabel,
          l2 (fun y => frameWeight i * Q r (action (frameKernel i) (Q z f)) y)) +
        l2 (Q r (action fourReturnKernel (Q z f))) :=
      by
        apply add_le_add
        · exact l2_finset_sum_le Finset.univ
            (fun i : FrameLabel => fun y =>
              frameWeight i * Q r (action (frameKernel i) (Q z f)) y)
        · exact le_rfl
    _ = (∑ i : FrameLabel,
          |frameWeight i| * l2 (Q r (action (frameKernel i) (Q z f)))) +
        l2 (Q r (action fourReturnKernel (Q z f))) := by simp only [l2_scale]
    _ ≤ (∑ i : FrameLabel, |frameWeight i| *
          (beta i.2.1 i.2.2 * l2 (Q z f))) + betaFour * l2 (Q z f) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (ReturnActualBranches.frame_l2 r i.1 z i.2.1 i.2.2 f) (abs_nonneg _)
      · exact ReturnActualBranches.four_l2 r z f
    _ = ((∑ i : FrameLabel, |frameWeight i| * beta i.2.1 i.2.2) + betaFour) *
        l2 (Q z f) := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [weighted_beta_sum]

/-- The assembled constant bounds the actual high return on component eleven. -/
theorem highReturn_profile_le_assembled (f : WordState → ℝ) :
    profile (TransferAssembly.highReturn (component f 11)) 11 ≤ assembled * profile f 11 := by
  have he := ReturnElevenBlocks.highReturn_profile_le_of_blocks (assembled / 4)
    (div_nonneg assembled_nonneg (by norm_num)) (fun g r z => physical_block_l2 r z g) f
  have hc : 4 * (assembled / 4) = assembled := by ring
  rwa [hc] at he

/-- The actual (11,11) return fits the exact existing physical recurrence allowance. -/
theorem highReturn_profile_le (f : WordState → ℝ) :
    profile (TransferAssembly.highReturn (component f 11)) 11 ≤
      TransferAssembly.physicalCoeff 2 11 11 (TransferAssembly.returnCoeff 11 11) *
        profile f 11 := by
  exact (highReturn_profile_le_assembled f).trans
    (mul_le_mul_of_nonneg_right ReturnElevenScalar.assembled_lt_allowance.le
      (l2_nonneg (component f 11)))

end AES8.ReturnEleven
