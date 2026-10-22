import AES8.Reductions.Return.PaperAESFixedStepTransport

/-!
# The physical fixed-position AES step bound

Frozen paper f902bb94, `lem:aesasm-step`, lines 426--484. The kernel is
the actual marked word graph sum between its outside residual maps and
input residual projection, for every physical split and both adjoints.
The conclusion is Q times its operator norm with the literal real-power
coefficient and the strict-shortening zero branch, including zero-sided
blocks. Complexification supplies arbitrary complex and signed inputs.
This is a fixed-position endpoint; grouped-state support lifting is separate.
Constructive proof validation only; no attacks or numerical searches.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESFixedStep
open AESMixing PaperMDSGram PaperKernelBounds
open PaperWordGraphCode PaperWordGraphDuality PaperAESIncidence
open PaperAESFixedStepBounds PaperAESFixedStepTransport
open AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

theorem physical_marked_card {i j : ℕ} (M : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) : M.card = i + j := by
  simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e

/-- Both representations bound the same physical operator; the smaller
code dimension gives exactly the paper's chosen rank and common-rank power. -/
theorem proper_real_norm {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4)
    (hd0 : 0 < d) (hdn : d < i + j) (adjoint : Bool) :
    (4294967296 : ℝ) * ‖kernelOperator (physicalStep M U e adjoint)‖ ≤
      PaperComparisonPowers.stepCoefficient i j (min d (i + j - d)) := by
  have hcard := physical_marked_card M e
  let C := physicalCode M U e
  have hC : IsMDS C d := physicalCode_isMDS M U e d hdim
  have hGraph : physicalStep M U e adjoint =
      kernelCompose (R i adjoint) (kernelCompose (K C d) (P j)) := by
    rw [physicalStep, physicalGraph_eq_K M U e hd d hdim (by omega)]
  rw [hGraph]
  by_cases hsmall : d ≤ i + j - d
  · have htrans := step_representation_norm C d (by omega) hC adjoint false
    have hnorm := reduced_real_norm C d hC (by omega) adjoint false
    have htrans' : ‖kernelOperator
        (kernelCompose (R i adjoint) (kernelCompose (K C d) (P j)))‖ ≤
        ‖kernelOperator (outsideMappedMatrix C (PaperGraphResponseMatrix.graphCoefficient i j d)
          (variant adjoint false))‖ := htrans
    simpa only [Nat.min_eq_left hsmall] using
      (mul_le_mul_of_nonneg_left htrans' (by norm_num)).trans hnorm
  · let s := i + j - d
    have hs : 2 * s ≤ i + j := by dsimp [s]; omega
    have hD : IsMDS (dual C) s := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using
        annihilator_isMDS AESConcrete.WordFourierCore.wordPairing C d (by simpa using (show d ≤ i+j by omega)) hC
    have htrans := step_representation_norm C d (by omega) hC adjoint true
    have htrans' : ‖kernelOperator
        (kernelCompose (R i adjoint) (kernelCompose (K C d) (P j)))‖ ≤
        ‖kernelOperator (outsideMappedMatrix (dual C) (PaperGraphResponseMatrix.graphCoefficient i j s)
          (variant adjoint true))‖ := htrans
    have hnorm := reduced_real_norm (dual C) s hD hs adjoint true
    simpa only [Nat.min_eq_right (show i + j - d ≤ d by omega), s] using
      (mul_le_mul_of_nonneg_left htrans' (by norm_num)).trans hnorm

/-- Physical shortening and literal activity counts identify the paper's
natural dimension, including the truncated nonpositive branch. -/
theorem physical_dimension {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (a b : ℕ)
    (hU : U.card = a + b) :
    4 - (zeroPositions M U).card = a + b + (i + j) - 4 := by
  have h := signed_dimension M U hd
  have hc := physical_marked_card M e
  omega

/-- The whole fixed-position step, including both strict-shortening zero
branches and either singleton side, on arbitrary signed-real input. -/
theorem physical_real_norm {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (hn : 0 < i + j)
    (a b : ℕ) (hU : U.card = a + b) (adjoint : Bool) :
    (4294967296 : ℝ) * ‖kernelOperator (physicalStep M U e adjoint)‖ ≤
      PaperComparisonPowers.paperStepGraph i a j b := by
  have hc := physical_marked_card M e
  have hdim := physical_dimension M U e hd a b hU
  unfold PaperComparisonPowers.paperStepGraph
  dsimp only
  rw [← hdim]
  by_cases hs : PaperComparison.survives (i+j) (4 - (zeroPositions M U).card)
  · rw [if_pos hs]
    exact proper_real_norm M U e hd (4 - (zeroPositions M U).card)
      (by dsimp [PaperComparison.survives] at hs; omega) hs.1 hs.2 adjoint
  · rw [if_neg hs]
    have hzero : physicalStep M U e adjoint = 0 := by
      by_cases hZ : 4 ≤ (zeroPositions M U).card
      · exact physicalStep_zero_branch M U e hn hZ adjoint
      · exact physicalStep_full_branch M U e hn
          (by dsimp [PaperComparison.survives] at hs; omega) adjoint
    rw [hzero]
    have hop : kernelOperator (0 : (Fin i → AES.Word) → (Fin j → AES.Word) → ℝ) = 0 := by
      ext f y
      simp [kernelOperator_apply, kernelAction]
    rw [hop, norm_zero, mul_zero]

/-- With a single marked residual coordinate strict shortening is
impossible, so the literal step kernel vanishes before any norm estimate. -/
theorem degree_one_zero {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hn : i + j = 1) (adjoint : Bool) :
    physicalStep M U e adjoint = 0 := by
  have hc := physical_marked_card M e
  by_cases hZ : 4 ≤ (zeroPositions M U).card
  · exact physicalStep_zero_branch M U e (by omega) hZ adjoint
  · exact physicalStep_full_branch M U e (by omega) (by omega) adjoint

/-- Literal multiplication by Q, before the real-to-complex transport. -/
theorem scaled_real_norm {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (hn : 0 < i + j)
    (a b : ℕ) (hU : U.card = a + b) (adjoint : Bool) :
    ‖kernelOperator (fun y x => (4294967296 : ℝ) * physicalStep M U e adjoint y x)‖ ≤
      PaperComparisonPowers.paperStepGraph i a j b := by
  have he : kernelOperator (fun y x => (4294967296 : ℝ) * physicalStep M U e adjoint y x) =
      (4294967296 : ℝ) • kernelOperator (physicalStep M U e adjoint) := by
    ext f y
    change (∑ x, (4294967296 : ℝ) * physicalStep M U e adjoint y x * f x) =
      (4294967296 : ℝ) * ∑ x, physicalStep M U e adjoint y x * f x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4294967296)]
  exact physical_real_norm M U e hd hn a b hU adjoint

theorem paperStepGraph_nonneg (i a j b : ℕ) :
    0 ≤ PaperComparisonPowers.paperStepGraph i a j b := by
  unfold PaperComparisonPowers.paperStepGraph
  dsimp only
  split_ifs
  · exact stepCoefficient_nonneg _ _ _
  · exact le_rfl

/-- All-complex-input energy form of the physical fixed-position lemma. -/
theorem physical_complex_energy {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (hn : 0 < i + j)
    (a b : ℕ) (hU : U.card = a + b) (adjoint : Bool)
    (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖kernelAction (fun y x =>
      (((4294967296 : ℝ) * physicalStep M U e adjoint y x : ℝ) : ℂ)) f y‖ ^ 2) ≤
      PaperComparisonPowers.paperStepGraph i a j b ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
  refine PaperWholeGraphReturn.complex_energy_of_real
    (fun y x => (4294967296 : ℝ) * physicalStep M U e adjoint y x)
    (PaperComparisonPowers.paperStepGraph i a j b ^ 2) ?_ f
  intro g
  exact PaperEncoding.local_energy_of_norm _ _ (paperStepGraph_nonneg i a j b)
    (scaled_real_norm M U e hd hn a b hU adjoint) g

/-- The literal Q-scaled physical operator is bounded by the frozen paper's
step array for every physical residual-position split, also if i=0 or j=0. -/
theorem physical_complex_norm {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (hn : 0 < i + j)
    (a b : ℕ) (hU : U.card = a + b) (adjoint : Bool) :
    ‖kernelOperator (fun y x =>
      (((4294967296 : ℝ) * physicalStep M U e adjoint y x : ℝ) : ℂ))‖ ≤
      PaperComparisonPowers.paperStepGraph i a j b := by
  have hn' := operator_norm_sq_le_of_energy _
    (PaperComparisonPowers.paperStepGraph i a j b ^ 2) (sq_nonneg _)
    (physical_complex_energy M U e hd hn a b hU adjoint)
  exact (sq_le_sq₀ (norm_nonneg _) (paperStepGraph_nonneg i a j b)).mp hn'

/-- The already-frozen scalar conversion identifies exactly the rational
array consumed downstream; it supplies no analytic premise. -/
theorem physical_stepGraph_norm {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (hd : Disjoint M U) (hn : 0 < i + j)
    (a b : ℕ) (hU : U.card = a + b) (adjoint : Bool) :
    ‖kernelOperator (fun y x =>
      (((4294967296 : ℝ) * physicalStep M U e adjoint y x : ℝ) : ℂ))‖ ≤
      (PaperComparison.stepGraph i a j b : ℝ) := by
  rw [PaperComparisonPowers.stepGraph_eq]
  exact physical_complex_norm M U e hd hn a b hU adjoint

end AES8.PaperAESFixedStep
