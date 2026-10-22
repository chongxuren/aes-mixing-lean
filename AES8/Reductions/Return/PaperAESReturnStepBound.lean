import AES8.Reductions.Return.PaperAESReturnMenu
import AES8.Reductions.Return.PaperAESReturnIdentification
import AES8.Reductions.Return.PaperAESFixedStep
import AES8.Math.PaperKernelReindex

/-! The actual two contracted AES steps satisfy the paper's return-term
minimum, including vanishing branches. The right input projection is kept
until its contraction bound is applied. The equal-bit entry resource remains
explicit; there is no assumed norm bound on the physical return. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESReturnStepBound
open AESMixing PaperKernelBounds PaperWordGraphCode PaperWordGraphDuality
open PaperAESActivityIdentification PaperAESFixedStepTransport
open PaperAESReturnIdentification PaperAESReturnMenu
open PaperAESFixedStep PaperAESIncidence
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem returnTerm_eq_bound (i a j b m mu lam : ℕ)
    (h : PaperComparison.survives (i+m) (a+mu+i+m-4) ∧
      PaperComparison.survives (j+m) (b+lam+j+m-4)) :
    PaperComparison.returnTerm i a j b m mu lam =
      bound i j m (a+mu+i+m-4) (b+lam+j+m-4) := by
  unfold PaperComparison.returnTerm
  dsimp only
  rw [if_pos h]
  rfl

theorem contracted_not_survives {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (hn : 0 < i+j)
    (h : ¬ PaperComparison.survives (i+j)
      (4 - (zeroPositions (marked O I) (uniform O I A B)).card)) :
    contracted O I A B eo ei false = 0 := by
  have hc := physical_marked_card (marked O I) (markedEquiv O I eo ei)
  by_cases hz : 4 ≤ (zeroPositions (marked O I) (uniform O I A B)).card
  · exact contracted_zero_branch O I A B eo ei false hn hz
  · exact contracted_full_branch O I A B eo ei false hn
      (by unfold PaperComparison.survives at h; omega)

/-- Literal physical frame counts; no support or independence hypothesis. -/
theorem uniform_card (O I A B : Finset (Fin 4)) :
    (uniform O I A B).card = (A \ O).card + (B \ I).card := by
  simp only [uniform, Finset.card_disjSum, Nat.add_comm]

/-- A single physical pair of steps, for every omitted-coordinate frame.
The zero cases are evaluated as kernels before taking operator norms. -/
theorem joined_scaled_norm {i j m : ℕ} (O I A B M C D : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (em : M ≃ Fin m)
    (hm : m = 3 ∨ m = 4)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (kernelCompose (contracted O M A C eo em false)
        (contracted M I D B em ei false))‖ ≤
      (PaperComparison.returnTerm i (A \ O).card j (B \ I).card m
        (C \ M).card (D \ M).card : ℝ) := by
  let a := (A \ O).card
  let b := (B \ I).card
  let mu := (C \ M).card
  let lam := (D \ M).card
  let dL := a+mu+i+m-4
  let dR := b+lam+j+m-4
  have hi : i ≤ 4 := by
    have hc : O.card = i := by simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr eo
    have hb := Finset.card_le_univ O
    simpa only [Fintype.card_fin, hc] using hb
  have hj : j ≤ 4 := by
    have hc : I.card = j := by simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr ei
    have hb := Finset.card_le_univ I
    simpa only [Fintype.card_fin, hc] using hb
  have hdL : 4 - (zeroPositions (marked O M) (uniform O M A C)).card = dL := by
    have h := physical_dimension (marked O M) (uniform O M A C)
      (markedEquiv O M eo em) (marked_uniform_disjoint O M A C) a mu (uniform_card O M A C)
    dsimp [dL]
    omega
  have hdR : 4 - (zeroPositions (marked M I) (uniform M I D B)).card = dR := by
    have h := physical_dimension (marked M I) (uniform M I D B)
      (markedEquiv M I em ei) (marked_uniform_disjoint M I D B) lam b (uniform_card M I D B)
    dsimp [dR]
    omega
  by_cases hs : PaperComparison.survives (i+m) dL ∧ PaperComparison.survives (j+m) dR
  · rw [returnTerm_eq_bound i a j b m mu lam hs]
    rw [joinedSteps_eq_physicalReturn O I A B M C D eo ei em]
    have hcap := proper_scaled_norm (marked O M) (uniform O M A C)
      (marked M I) (uniform M I D B) (markedEquiv O M eo em) (rightEquiv I M ei em)
      (marked_uniform_disjoint O M A C) (marked_uniform_disjoint M I D B) dL dR
      (by have := hs.1.1; omega) (by have := hs.2.1; omega)
      hi hj hm hs.1.1 hs.1.2 hs.2.1 hs.2.2 hentry
    apply le_trans _ hcap
    apply mul_le_mul_of_nonneg_left _ (by norm_num [PaperComparison.q])
    exact (compose_norm_le_right _ _ (P_norm j)).trans
      (PaperKernelReindex.real_kernel_norm_le_complex _)
  · have hz : kernelCompose (contracted O M A C eo em false)
        (contracted M I D B em ei false) = 0 := by
      by_cases hl : PaperComparison.survives (i+m) dL
      · have hr : ¬ PaperComparison.survives (m+j)
            (4 - (zeroPositions (marked M I) (uniform M I D B)).card) := by
          rw [hdR, Nat.add_comm m j]
          exact fun h => hs ⟨hl,h⟩
        rw [contracted_not_survives M I D B em ei (by omega) hr]
        funext y x
        simp [kernelCompose]
      · rw [contracted_not_survives O M A C eo em (by omega) (by simpa only [hdL] using hl)]
        funext y x
        simp [kernelCompose]
    have ht : PaperComparison.returnTerm i a j b m mu lam = 0 := by
      unfold PaperComparison.returnTerm
      dsimp only
      exact if_neg hs
    rw [ht, hz]
    have ho : kernelOperator (0 : (Fin i → AES.Word) → (Fin j → AES.Word) → ℝ) = 0 := by
      ext f y
      simp [kernelOperator_apply, kernelAction]
    rw [ho, norm_zero, mul_zero, Rat.cast_zero]

end AES8.PaperAESReturnStepBound
