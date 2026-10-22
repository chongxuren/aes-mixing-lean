import AES8.Reductions.Return.PaperAESReturnStepBound
import AES8.Reductions.Return.PaperSharedReturnNorm
import AES8.Estimates.Transfer.PaperRationalSupportLift

/-! The common return graph bounds each actual outside frame. The two
physical legs share one middle metric, including its off-diagonal signs.
The finite equal-bit entry resource is the only remaining analytic premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnFrameBound
open AESMixing PaperKernelBounds PaperWordGraphCode PaperWordGraphDuality
open PaperAESActivityIdentification PaperAESFixedStepTransport
open PaperAESReturnIdentification PaperAESReturnStepBound
open PaperActivityMinorTransport
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem middle_uniform_count (c : Fin 4) (s : Bool) :
    (middleUniform c s \ middle c).card = if s then 1 else 0 := by
  cases s
  · simp [middleUniform]
  · have he : ({c} : Finset (Fin 4)) \ middle c = {c} := by
      ext k
      simp [middle]
    simp only [middleUniform, if_true, he, Finset.card_singleton]

theorem branch_scaled_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (c : Fin 4) (s t : Bool)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 * ‖kernelOperator (contractedBranch O I A B eo ei c s t)‖ ≤
      (PaperComparison.returnTerm i (A \ O).card j (B \ I).card 3
        (if s then 1 else 0) (if t then 1 else 0) : ℝ) := by
  let em : middle c ≃ Fin 3 := Finset.equivFinOfCardEq (middle_card c)
  rw [contractedBranch_eq_steps O I A B eo ei c em s t]
  simpa only [middle_uniform_count] using
    joined_scaled_norm O I A B (middle c) (middleUniform c s) (middleUniform c t)
      eo ei em (Or.inl rfl) hentry

theorem four_scaled_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 * ‖kernelOperator (contractedFour O I A B eo ei)‖ ≤
      (PaperComparison.returnTerm i (A \ O).card j (B \ I).card 4 0 0 : ℝ) := by
  let em : (Finset.univ : Finset (Fin 4)) ≃ Fin 4 := Finset.equivFinOfCardEq (by simp)
  rw [contractedFour_eq_steps O I A B eo ei em]
  simpa only [Finset.empty_sdiff, Finset.card_empty] using
    joined_scaled_norm O I A B Finset.univ ∅ ∅ eo ei em (Or.inr rfl) hentry

/-- Every outside physical frame uses the same signed middle expansion.
There is exactly one inverse-metric factor, after the two legs are joined. -/
theorem high_scaled_norm {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (outsideContract O I A B eo ei ReturnCentering.physicalReturnKernel)‖ ≤
      (PaperComparison.returnGraph i (A \ O).card j (B \ I).card : ℝ) := by
  let q3 : ℝ := (PaperComparison.q : ℝ)^3
  have hq : 0 < q3 := by norm_num [q3, PaperComparison.q]
  let g : Bool → Bool → ℝ := fun s t =>
    (PaperComparison.returnTerm i (A \ O).card j (B \ I).card 3
      (if s then 1 else 0) (if t then 1 else 0) : ℝ) / q3
  let g4 : ℝ := (PaperComparison.returnTerm i (A \ O).card j (B \ I).card 4 0 0 : ℝ) / q3
  let L := kernelOperator (fun y : Fin i → AES.Word => analysis O (fun k => decide (k ∈ A)) (fun p => y (eo p)))
  let R := kernelOperator (fun (a : AES.WordState) (x : Fin j → AES.Word) => synthesis I (fun k => decide (k ∈ B)) a (fun p => x (ei p)))
  have h3 (l : PaperSharedReturnNorm.FrameLabel) :
      ‖L.comp ((kernelOperator (PaperSharedReturnNorm.branch l)).comp R)‖ ≤ g l.2.1 l.2.2 := by
    have h : ‖kernelOperator (contractedBranch O I A B eo ei l.1 l.2.1 l.2.2)‖ ≤ g l.2.1 l.2.2 := (le_div_iff₀ hq).mpr (by
      simpa only [mul_comm] using branch_scaled_norm O I A B eo ei l.1 l.2.1 l.2.2 hentry)
    simpa only [contractedBranch, outsideContract, PaperAESIncidence.kernelOperator_comp, L, R, PaperSharedReturnNorm.branch] using h
  have h4 : ‖L.comp ((kernelOperator PhysicalZeroPattern.fourReturnKernel).comp R)‖ ≤ g4 := by
    have h : ‖kernelOperator (contractedFour O I A B eo ei)‖ ≤ g4 := (le_div_iff₀ hq).mpr (by
      simpa only [mul_comm] using four_scaled_norm O I A B eo ei hentry)
    simpa only [contractedFour, outsideContract, PaperAESIncidence.kernelOperator_comp] using h
  have h := mul_le_mul_of_nonneg_left (PaperSharedReturnNorm.outside_norm L R g g4 h3 h4) hq.le
  have hs : q3 * (4 * WordActivityFrame.eta AES.Word *
      (g false false + WordActivityFrame.xi AES.Word * g false true +
        WordActivityFrame.xi AES.Word * g true false + g true true) + g4) =
      (PaperComparison.returnGraph i (A \ O).card j (B \ I).card : ℝ) := by
    rw [PaperRationalSupportLift.eta_eq, PaperRationalSupportLift.xi_eq]
    dsimp [g, g4, PaperComparison.returnGraph]
    push_cast
    field_simp [hq.ne']
    <;> ring
  rw [hs] at h
  simpa only [outsideContract, PaperAESIncidence.kernelOperator_comp] using h

end AES8.PaperAESReturnFrameBound
