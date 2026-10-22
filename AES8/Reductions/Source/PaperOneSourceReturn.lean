import AES8.Reductions.Source.PaperFixedSupportReturn

/-! Rational fixed-support coefficients for the two one-source degrees.
Only the output position count is rounded; the fixed input count equals one.
This is an operator bound and does not assume independence of a signed input. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperOneSourceReturn
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift
open PaperExactSupportLift PaperRationalSupportLift
set_option autoImplicit false
set_option maxHeartbeats 2000000

def coefficient (i t j : ℕ) : ℚ :=
  PaperComparison.rootUpper (PaperComparison.positionCount i t) *
    PaperComparison.eta^(t-i+1-j) *
      PaperComparison.supportSum i t j 1 PaperComparison.returnGraph

theorem coefficient_le (i t : Fin 5) (j : Fin 2) :
    fixedBound AES.Word i.val t.val j.val 1
        (PaperAESSupportReturnBound.graphCap i.val j.val) *
      Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        Nat.choose 1 j.val) ≤
      (coefficient i.val t.val j.val : ℝ) / (PaperComparison.q : ℝ)^3 := by
  have hj : j.val ≤ 1 := by omega
  have hchoose : Nat.choose 1 j.val = 1 := by fin_cases j <;> decide
  have hsum := supportSum_nonneg i.val t.val j.val 1 PaperComparison.returnGraph
    (fun a b => PaperComparison.returnGraph_nonneg i.val a j.val b)
  have hc : (0 : ℝ) < (PaperComparison.q : ℝ)^3 := by norm_num [PaperComparison.q]
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) eta_sqrt_le
    (t.val-i.val+(1-j.val))
  have hexp : t.val-i.val+(1-j.val) = t.val-i.val+1-j.val := by omega
  unfold fixedBound PaperAESSupportReturnBound.graphCap
  rw [supportSum_div, supportSum_cast _ _ _ _ hj, hchoose]
  simp only [Nat.cast_one, mul_one]
  change _ * Real.sqrt (PaperComparison.positionCount i.val t.val : ℝ) ≤ _
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_right hpow (div_nonneg hsum hc.le))
    (position_sqrt_le i t) (Real.sqrt_nonneg _)
    (mul_nonneg (by unfold PaperComparison.eta PaperComparison.q; positivity)
      (div_nonneg hsum hc.le))
  rw [hexp] at h
  unfold coefficient
  push_cast
  simpa only [hexp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem norm_le (i t : Fin 5) (j : Fin 2) (mask : Fin 4 → Bool)
    (hmask : supportCount mask = 1)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action ReturnCentering.physicalReturnKernel (fixedComponent 0 f j.val mask))
      i.val t.val) ≤
      ((coefficient i.val t.val j.val : ℝ) / (PaperComparison.q : ℝ)^3) *
        l2 (fixedComponent (0 : AES.Word) f j.val mask) := by
  have h := PaperFixedSupportReturn.norm_le i t ⟨j.val, by omega⟩ mask hentry f
  simp only [hmask] at h
  exact h.trans (mul_le_mul_of_nonneg_right (coefficient_le i t j) (l2_nonneg _))

end AES8.PaperOneSourceReturn
