import AES8.Reductions.Support.PaperExactSupportLift
import AES8.Recurrence.PaperComparisonGraphs
import AESConcrete.WordFourierCore

/-! The exact support-lift coefficient is bounded by the paper's rational
array. This numerical adapter supplies no physical operator premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperRationalSupportLift
open AESMixing PaperExactSupportLift
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem eta_eq : WordActivityFrame.eta AES.Word = (PaperComparison.eta : ℝ) := by
  norm_num [WordActivityFrame.eta, WordActivityFrame.q,
    AESConcrete.WordFourierCore.word_card, BinaryWord.card, PaperComparison.eta, PaperComparison.q]

theorem xi_eq : WordActivityFrame.xi AES.Word = (PaperComparison.xi : ℝ) := by
  have hs : Real.sqrt (4294967296 : ℝ) = 65536 := by
    rw [show (4294967296 : ℝ) = 65536^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp only [WordActivityFrame.xi, WordActivityFrame.q,
    AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat, hs]
  norm_num [PaperComparison.xi, PaperComparison.sqrtQ]

theorem eta_sqrt_le : Real.sqrt (WordActivityFrame.eta AES.Word) ≤
    (PaperComparison.eta : ℝ) := by
  rw [eta_eq]
  apply (Real.sqrt_le_iff).mpr
  norm_num [PaperComparison.eta, PaperComparison.q]

/-- All 25 support/residual index pairs, including empty invalid blocks. -/
theorem position_sqrt_le (i t : Fin 5) :
    Real.sqrt (PaperComparison.positionCount i.val t.val : ℝ) ≤
      (PaperComparison.rootUpper (PaperComparison.positionCount i.val t.val) : ℝ) := by
  fin_cases i <;> fin_cases t <;>
    norm_num [PaperComparison.positionCount, PaperComparison.rootUpper, Nat.choose,
      Real.sqrt_le_iff]

theorem supportSum_cast (i t j u : ℕ) (hju : j ≤ u)
    (G : ℕ → ℕ → ℕ → ℕ → ℚ) :
    PaperActivityExpansion.supportSum (t-i) (u-j) (WordActivityFrame.xi AES.Word)
      (fun a b => (G i a j b : ℝ)) = (PaperComparison.supportSum i t j u G : ℝ) := by
  unfold PaperActivityExpansion.supportSum PaperComparison.supportSum
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' : a ≤ t-i := by have := Finset.mem_range.mp ha; omega
  have hb' : b ≤ u-j := by have := Finset.mem_range.mp hb; omega
  have hexp : (t-i-a)+(u-j-b) = t-i+u-j-a-b := by omega
  rw [xi_eq]
  rw [← hexp, pow_add]
  ring

theorem supportSum_div (n m : ℕ) (x c : ℝ) (G : ℕ → ℕ → ℝ) :
    PaperActivityExpansion.supportSum n m x (fun a b => G a b / c) =
      PaperActivityExpansion.supportSum n m x G / c := by
  unfold PaperActivityExpansion.supportSum
  simp only [← mul_div_assoc, ← Finset.sum_div]

theorem supportSum_nonneg (i t j u : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℚ)
    (hG : ∀ a b, 0 ≤ G i a j b) :
    (0 : ℝ) ≤ (PaperComparison.supportSum i t j u G : ℝ) := by
  have h : (0 : ℚ) ≤ PaperComparison.supportSum i t j u G := by
    unfold PaperComparison.supportSum
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg _ (hG a b)
    unfold PaperComparison.xi PaperComparison.sqrtQ
    positivity
  exact_mod_cast h

/-- The paper rounds sqrt(eta) upward and both position-count roots upward. -/
theorem coefficient_le (i t j u : Fin 5) (hju : j.val ≤ u.val)
    (G : ℕ → ℕ → ℕ → ℕ → ℚ) (hG : ∀ a b, 0 ≤ G i.val a j.val b)
    (c : ℝ) (hc : 0 < c) :
    fixedBound AES.Word i.val t.val j.val u.val
        (fun a b => (G i.val a j.val b : ℝ) / c) *
      Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        (Nat.choose 4 u.val * Nat.choose u.val j.val)) ≤
      (PaperComparison.support i.val t.val j.val u.val G : ℝ) / c := by
  have hsum := supportSum_nonneg i.val t.val j.val u.val G hG
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) eta_sqrt_le
    (t.val-i.val+(u.val-j.val))
  have hroots := mul_le_mul (position_sqrt_le i t) (position_sqrt_le j u)
    (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (position_sqrt_le i t))
  have hexp : t.val-i.val+(u.val-j.val) = t.val-i.val+u.val-j.val := by omega
  unfold fixedBound
  rw [supportSum_div, supportSum_cast _ _ _ _ hju]
  rw [← Nat.cast_mul]
  change _ * Real.sqrt ((PaperComparison.positionCount i.val t.val : ℝ) *
    (PaperComparison.positionCount j.val u.val : ℝ)) ≤ _
  rw [Real.sqrt_mul (by positivity)]
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_right hpow (div_nonneg hsum hc.le)) hroots
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by unfold PaperComparison.eta PaperComparison.q; positivity)
      (div_nonneg hsum hc.le))
  rw [hexp] at h
  unfold PaperComparison.support
  push_cast
  simpa only [hexp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end AES8.PaperRationalSupportLift
