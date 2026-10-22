import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Reductions.Return.PaperAESActivityIdentification
import AES8.Math.PaperMDSGram
import AES8.Estimates.Word.PaperWordTwoSwapsVariants

/-! Actual MDS graph responses for activity inputs. The frame coefficient is
restored exactly from the graph's own shortening count and code cardinality.
No operator, frame or scalar response cap is assumed. Boolean aggregation
and full degree lifting remain separate from this fixed graph response. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputResponse
open AESMixing PaperWordGraphCode PaperMDSGram
open AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def wordQ : ℝ := 4294967296
def tau : ℝ := 300 / wordQ
def beta : ℝ := 2 / (15 * wordQ)

theorem word_card : (Fintype.card AES.Word : ℝ) = wordQ := by
  rw [AES.word_card]; norm_num [wordQ]

def response (M U : Finset Position) (adjoint : Bool) (y : M → AES.Word) : ℝ :=
  action (coordinateKernel (fun _ : M => baseResidual adjoint))
    (graphContraction M U) y

def responseMoment (n d : ℕ) : ℝ :=
  (tau ^ 2 / wordQ) ^ min d (n-d) * beta ^ (n-2*min d (n-d))

theorem actual_unit_energy (M U : Finset Position) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hd0 : 0 < d) (hdn : d < M.card)
    (adjoint : Bool) :
    (∑ y : M → AES.Word,
      action (coordinateKernel (fun _ : M => baseResidual adjoint))
        (unitSubgroupIndicator (markedCode M U)) y ^ 2) ≤ responseMoment M.card d := by
  have hc := paper_mixed_mds_gram_bound AESConcrete.WordFourierCore.wordPairing
    word_add_self
    (fun _ : M => baseResidual adjoint) (markedCode M U) d hd0
    (by simpa only [Fintype.card_coe] using hdn) (markedCode_isMDS M U d hdim)
    tau beta
    (fun _ => by
      have h := (PaperWordTwoSwapsVariants.variant_gram_moment_lt adjoint false).le
      simpa only [variant, Bool.false_eq_true, if_false, Fintype.sum_prod_type,
        tau, wordQ, gram] using h)
    (fun _ a => by
      rw [gram_diagonal]
      have h := (PaperAESSource.residualVariant_column_energy_lt_current adjoint false a).le
      simpa only [variant, Bool.false_eq_true, if_false, beta, wordQ] using h)
    (fun _ _ a => by
      rw [gram_diagonal]
      have h := (PaperAESSource.residualVariant_column_energy_lt_current adjoint true a).le
      simpa only [variant, if_true, AESConcrete.WordFourierCore.wordConjugate,
        beta, wordQ] using h)
  simpa only [Fintype.card_coe, word_card, responseMoment] using hc

/-- Literal normalized-code response, retaining its actual signed coefficient. -/
theorem response_eq_unit (M U : Finset Position) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card)
    (adjoint : Bool) (y : M → AES.Word) :
    response M U adjoint y =
      (WordActivityFrame.xi AES.Word ^ U.card *
        Real.sqrt (Fintype.card (markedCode M U) : ℝ)) *
      action (coordinateKernel (fun _ : M => baseResidual adjoint))
        (unitSubgroupIndicator (markedCode M U)) y := by
  have hcard : 0 < (Fintype.card (markedCode M U) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := markedCode M U)
  have hs : Real.sqrt (Fintype.card (markedCode M U) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hcard).ne'
  have hg (z : M → AES.Word) : graphContraction M U z =
      (WordActivityFrame.xi AES.Word ^ U.card *
        Real.sqrt (Fintype.card (markedCode M U) : ℝ)) *
        unitSubgroupIndicator (markedCode M U) z := by
    rw [graphContraction_eq M U d hdim hlarge, ← frame_scalar_rpow]
    unfold unitSubgroupIndicator
    by_cases hz : z ∈ markedCode M U <;> simp [hz, hs]
  unfold response action
  simp_rw [hg]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Exact square of the frame-to-unit-indicator coefficient. -/
theorem coefficient_sq (M U : Finset Position) (hd : Disjoint M U) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card)
    (hn : M.card ≤ 4) :
    (WordActivityFrame.xi AES.Word ^ U.card *
      Real.sqrt (Fintype.card (markedCode M U) : ℝ)) ^ 2 =
        1 / wordQ ^ (4-M.card) := by
  have hc : U.card = d + (4-M.card) := by
    have h := activity_count M U hd d hdim
    omega
  rw [mul_pow, ← pow_mul, Nat.mul_comm U.card 2, pow_mul,
    WordActivityFrame.xi_sq AESConcrete.AES.word_card_gt_one,
    Real.sq_sqrt (Nat.cast_nonneg _), markedCode_card M U d hdim hlarge,
    Nat.cast_pow]
  rw [WordActivityFrame.q, word_card]
  rw [hc, pow_add, div_pow, div_pow]
  field_simp [show wordQ ≠ 0 by norm_num [wordQ]]
  ring

/-- The fixed-response squared norm in the paper's exact q normalization. -/
theorem response_energy (M U : Finset Position) (hd : Disjoint M U) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hd0 : 0 < d) (hdn : d < M.card)
    (hn : M.card ≤ 4) (adjoint : Bool) :
    (∑ y : M → AES.Word, response M U adjoint y ^ 2) ≤
      responseMoment M.card d / wordQ ^ (4-M.card) := by
  simp_rw [response_eq_unit M U d hdim hdn.le adjoint]
  rw [show (∑ y : M → AES.Word,
      ((WordActivityFrame.xi AES.Word ^ U.card * Real.sqrt (Fintype.card (markedCode M U) : ℝ)) *
      action (coordinateKernel (fun _ : M => baseResidual adjoint))
        (unitSubgroupIndicator (markedCode M U)) y)^2) =
      (WordActivityFrame.xi AES.Word ^ U.card * Real.sqrt (Fintype.card (markedCode M U) : ℝ))^2 *
      ∑ y : M → AES.Word, action (coordinateKernel (fun _ : M => baseResidual adjoint))
        (unitSubgroupIndicator (markedCode M U)) y ^ 2 by
    simp_rw [mul_pow]; rw [← Finset.mul_sum]]
  rw [coefficient_sq M U hd d hdim hdn.le hn]
  have h := mul_le_mul_of_nonneg_left (actual_unit_energy M U d hdim hd0 hdn adjoint)
    (show 0 ≤ 1 / wordQ ^ (4-M.card) by unfold wordQ; positivity)
  simpa only [one_div_mul_eq_div] using h

/-- The graph branches excluded by `0 < d < i` vanish by actual channel
zero-column and zero-row-sum identities, before any moment estimate. -/
theorem response_zero_branch (M U : Finset Position) (hn : 0 < M.card)
    (hZ : 4 ≤ (zeroPositions M U).card) (adjoint : Bool) :
    response M U adjoint = 0 := by
  funext y
  change response M U adjoint y = (0 : ℝ)
  unfold response action
  simp_rw [graphContraction_zero_branch M U hZ]
  simp only [mul_ite, mul_zero, mul_one]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hM : Nonempty M := Fintype.card_pos_iff.mp (by simpa using hn)
  obtain ⟨p⟩ := hM
  have hz : coordinateKernel (fun _ : M => baseResidual adjoint) y 0 = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    exact PaperAESFixedStepTransport.R_zero_column adjoint (y p)
  rw [hz,zero_mul]

theorem response_full_branch (M U : Finset Position) (hn : 0 < M.card)
    (hfull : (zeroPositions M U).card + M.card ≤ 4) (adjoint : Bool) :
    response M U adjoint = 0 := by
  funext y
  change response M U adjoint y = (0 : ℝ)
  unfold response action
  simp_rw [graphContraction_full_branch M U hfull]
  rw [← Finset.sum_mul]
  have hM : Nonempty M := Fintype.card_pos_iff.mp (by simpa using hn)
  obtain ⟨p⟩ := hM
  have hz : (∑ z : M → AES.Word, coordinateKernel (fun _ : M => baseResidual adjoint) y z) = 0 := by
    unfold coordinateKernel
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    exact PaperAESFixedStepTransport.R_row_sum adjoint (y p)
  rw [hz,zero_mul]

theorem degree_two_energy (M U : Finset Position) (hd : Disjoint M U)
    (hn : M.card = 2) (hdim : (zeroPositions M U).card + 1 = 4) (adjoint : Bool) :
    (∑ y : M → AES.Word, response M U adjoint y ^ 2) ≤ tau^2/wordQ^3 := by
  have h := response_energy M U hd 1 hdim (by omega) (by omega) (by omega) adjoint
  simpa [hn, responseMoment, div_pow, div_div, pow_succ, mul_comm,
    mul_left_comm, mul_assoc] using h

theorem degree_three_energy (M U : Finset Position) (hd : Disjoint M U)
    (hn : M.card = 3) (d : ℕ) (hd0 : 0 < d) (hdn : d < 3)
    (hdim : (zeroPositions M U).card + d = 4) (adjoint : Bool) :
    (∑ y : M → AES.Word, response M U adjoint y ^ 2) ≤ tau^2*beta/wordQ^2 := by
  have h := response_energy M U hd d hdim hd0 (by omega) (by omega) adjoint
  have hd : d = 1 ∨ d = 2 := by omega
  rcases hd with rfl | rfl <;> apply h.trans_eq <;>
    simp only [hn, responseMoment] <;> norm_num <;> ring

theorem degree_four_line_energy (M U : Finset Position) (hd : Disjoint M U)
    (hn : M.card = 4) (d : ℕ) (hline : d = 1 ∨ d = 3)
    (hdim : (zeroPositions M U).card + d = 4) (adjoint : Bool) :
    (∑ y : M → AES.Word, response M U adjoint y ^ 2) ≤ tau^2*beta^2/wordQ := by
  have h := response_energy M U hd d hdim (by omega) (by omega) (by omega) adjoint
  rcases hline with rfl | rfl <;> apply h.trans_eq <;>
    simp only [hn, responseMoment] <;> norm_num <;> ring

theorem degree_four_plane_energy (M U : Finset Position) (hd : Disjoint M U)
    (hn : M.card = 4) (hdim : (zeroPositions M U).card + 2 = 4) (adjoint : Bool) :
    (∑ y : M → AES.Word, response M U adjoint y ^ 2) ≤ tau^4/wordQ^2 := by
  have h := response_energy M U hd 2 hdim (by omega) (by omega) (by omega) adjoint
  apply h.trans_eq
  simp only [hn, responseMoment]
  norm_num
  ring

end AES8.PaperAESActivityInputResponse
