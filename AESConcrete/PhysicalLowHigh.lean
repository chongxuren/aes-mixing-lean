import AESConcrete.PhysicalProjectionSystem
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Exact low-map certificate filter and high-degree kernel

The source residual-word degree selects low columns zero through ten.
The frozen H matrix is exactly L with the three high-source columns
removed. Consequently every low operator cap follows from its matching
physical step cap, and the high columns are zero without a step premise.
No additional normalization factor or numerical cap is introduced.

The actual high kernel is degree three plus degree four. This statement
concerns the full counting-measure space. The complementary low sum omits
the all-zero-state projector; the existing remainder-invisibility assembly
accounts for that projector separately.

Constructive mathematics only; no attacks, local workloads, manuscript or
historical edits. Independent retained uniform keys, whitening, omitted
final MixColumns and ordered distinct pairs stay fixed. This separate
candidate changes no public root, Audit, existing source or certificate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.PhysicalLowHigh
open AESMixing
open AESConcrete.RefinedWordProjection (refinedKernel)
open AESConcrete.RefinedStepZeros (blockType physicalBlock)
open AESConcrete.RefinedProjectionCompleteness (refined_invalid refined_sum_active)
open AESConcrete.PhysicalProjectionSystem (State system decomposition isLow projectionKernel
  highKernel step_eq_physical low_eq_physical highProject_eq_kernel operator_add)

set_option maxRecDepth 4096

section GenericLow
variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This exact norm identity requires no nonnegative-cap hypothesis. -/
theorem low_norm_eq (G : AESRound.ProjectionAssembly.Decomposition I E)
    (flag : I → Bool) (i j : I) :
    ‖G.low flag i j‖ = if flag j then ‖G.step i j‖ else 0 := by
  change ‖if flag j then G.step i j else 0‖ = _
  cases h : flag j <;> simp [h]

theorem low_norm_le_of_step (G : AESRound.ProjectionAssembly.Decomposition I E)
    (flag : I → Bool) (A : I → I → ℝ)
    (hstep : ∀ i j, ‖G.step i j‖ ≤ A i j) (i j : I) :
    ‖G.low flag i j‖ ≤ if flag j then A i j else 0 := by
  rw [low_norm_eq]
  cases h : flag j
  · simp [h]
  · simpa only [h, if_true] using hstep i j

end GenericLow

theorem isLow_eq_decide_index (j : Fin 14) : isLow j = decide (j.val ≤ 10) := by
  fin_cases j <;> rfl

theorem isLow_iff_index (j : Fin 14) : isLow j = true ↔ j.val ≤ 10 := by
  fin_cases j <;> decide

theorem isHigh_iff_index (j : Fin 14) : isLow j = false ↔ 10 < j.val := by
  fin_cases j <;> decide

/-- This finite label identity compares the exact frozen entries. It is
not an operator bound or a new certificate generation step. -/
theorem certificate_H_eq_filtered_L (i j : Fin 14) :
    AESRound.Certificate.H i j = if isLow j then AESRound.Certificate.L i j else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem concrete_low_norm_eq (i j : Fin 14) :
    ‖system.low i j‖ = if isLow j then ‖kernelOperator (physicalBlock i j)‖ else 0 := by
  rw [low_eq_physical]
  cases h : isLow j <;> simp [h]

/-- Only the corresponding low-source step cap is needed. For a high
source the actual low map and its certificate entry are exactly zero. -/
theorem low_caps_of_low_source_step_caps
    (hstep : ∀ (i j : Fin 14), isLow j = true →
      ‖kernelOperator (physicalBlock i j)‖ ≤
        AESRound.Terminal.lambda * AESRound.Certificate.L i j) :
    ∀ i j, ‖system.low i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.H i j := by
  intro i j
  rw [concrete_low_norm_eq, certificate_H_eq_filtered_L]
  cases h : isLow j
  · simp [h]
  · simpa only [h, if_true] using hstep i j h

theorem low_caps_of_step_caps
    (hstep : ∀ (i j : Fin 14), ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j) :
    ∀ i j, ‖system.low i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.H i j :=
  low_caps_of_low_source_step_caps (fun i j _ => hstep i j)

theorem low_caps_of_system_step_caps
    (hstep : ∀ (i j : Fin 14), ‖system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j) :
    ∀ i j, ‖system.low i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.H i j := by
  apply low_caps_of_step_caps
  intro i j
  simpa only [step_eq_physical] using hstep i j

theorem degree_three_refined {V : Type*} [Fintype V] [DecidableEq V] (z : V) :
    degreeKernel z 3 = refinedKernel z 3 3 + refinedKernel z 3 4 := by
  rw [← refined_sum_active z 3]
  funext y x
  simp [Fin.sum_univ_succ,
    refined_invalid z 3 0 (by decide), refined_invalid z 3 1 (by decide),
    refined_invalid z 3 2 (by decide), add_assoc]

theorem degree_four_refined {V : Type*} [Fintype V] [DecidableEq V] (z : V) :
    degreeKernel z 4 = refinedKernel z 4 4 := by
  rw [← refined_sum_active z 4]
  funext y x
  simp [Fin.sum_univ_succ,
    refined_invalid z 4 0 (by decide), refined_invalid z 4 1 (by decide),
    refined_invalid z 4 2 (by decide), refined_invalid z 4 3 (by decide)]

/-- The high partition uses residual-word degrees, not active counts.
The three remaining types are (3,3), (3,4) and (4,4). -/
theorem highKernel_eq_degrees :
    highKernel = degreeKernel (0 : AES.Word) 3 + degreeKernel (0 : AES.Word) 4 := by
  rw [degree_three_refined, degree_four_refined]
  funext y x
  simp [highKernel, projectionKernel, isLow, blockType, Fin.sum_univ_succ, add_assoc]

theorem highProject_eq_degrees :
    decomposition.highProject isLow =
      kernelOperator (degreeKernel (0 : AES.Word) 3) +
        kernelOperator (degreeKernel (0 : AES.Word) 4) := by
  rw [highProject_eq_kernel, highKernel_eq_degrees, operator_add]

end AESConcrete.PhysicalLowHigh
