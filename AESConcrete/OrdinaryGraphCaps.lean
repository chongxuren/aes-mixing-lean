import AESConcrete.GeneralMDSGraphEnergy
import AESConcrete.ResidualIncidenceAggregation
import AESConcrete.PhysicalProjectionSystem
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Ordinary graph family for five actual row-13 caps

A support piece with `b` active coordinates receives `rho^(2*b) * kappa^(4-b)`
in counting energy. Genuine input support orthogonality and output Cauchy--
Schwarz aggregate all pieces, with their exact selected-support multiplicity.
Arbitrary joint signed inputs are retained. Output orthogonality is neither
required nor asserted.

The general energy theorem precedes exact comparisons with the five frozen
caps. Inventory and overlap belong to `OrdinaryGraphStepCaps`, not this
analytic module. Independent uniform retained keys, whitening, omitted final
MixColumns and ordered-distinct pairs stay fixed. No return cap or complete
AES 10/14/16 theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OrdinaryGraphCaps
open AESMixing
open AESConcrete.RefinedWordProjection (refinedKernel supportIndexKernel)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport selectedSupport_card)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

local notation "ρ" => (21 / 131072 : ℝ)
local notation "κ" => (2 / (15 * 4294967296) : ℝ)

/-- An energy coefficient, not an operator norm or a certificate entry. -/
def graphSquaredBound (d b : Fin 5) : ℝ :=
  (ResidualIncidenceCoefficient.multiplicity d b : ℝ) * ρ ^ (2 * b.val) * κ ^ (4 - b.val)

theorem graphSquaredBound_nonneg (d b : Fin 5) : 0 ≤ graphSquaredBound d b := by
  unfold graphSquaredBound
  positivity

section SelectedInput
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only the selected input energies are summed. Their exact support
orthogonality is inherited from the whole-degree decomposition. -/
theorem selected_input_energy_le (z : V) (hn : 1 < Fintype.card V)
    (d b : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ p : SelectedSupport d b, ∑ x, supportIndexComponent z p.val f x ^ 2) ≤
      ∑ x, f x ^ 2 := by
  let s : Finset (SupportIndex d.val) :=
    Finset.univ.filter (fun p => AES.maskSize p.val.2 + b.val = 4)
  have hs : (∑ p : SelectedSupport d b, ∑ x,
      supportIndexComponent z p.val f x ^ 2) =
      ∑ p ∈ s, ∑ x, supportIndexComponent z p f x ^ 2 := by
    symm
    exact Finset.sum_subtype _ (by simp [s]) _
  rw [hs]
  calc
    _ ≤ ∑ p : SupportIndex d.val, ∑ x, supportIndexComponent z p f x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro p _ _
      exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
    _ = ∑ x, degreeComponent z d f x ^ 2 := (supportIndex_degree_energy z hn d f).symm
    _ ≤ ∑ x, f x ^ 2 := degreeComponent_energy_le z hn d f

end SelectedInput

section FiniteSum

/-- Finite output aggregation by Cauchy--Schwarz for arbitrary signs. -/
theorem sum_sq_le_card {I : Type*} [Fintype I] (a : I → ℝ) :
    (∑ i, a i) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, a i ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ)) a

private theorem action_fintype_sum {I X Y : Type*} [Fintype I] [Fintype X]
    (K : Y → X → ℝ) (f : I → X → ℝ) :
    action K (fun x => ∑ i, f i x) = fun y => ∑ i, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteSum

/-- Every selected piece receives the arbitrary-active-count graph estimate
in the actual residual-step indexing. -/
theorem selected_piece_energy (d b : Fin 5) (p : SelectedSupport d b)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤
      ρ ^ (2 * b.val) * κ ^ (4 - b.val) *
        ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
  have h := GeneralMDSGraphEnergy.word_residual_support_piece_energy p.val b p.property f
  change (∑ y, action
    (fun y x => residualTensor y (wordMixAddEquiv.toEquiv x))
    (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤ _
  rw [FourResidualStep.input_permutation_action residualTensor wordMixAddEquiv.toEquiv]
  exact h

/-- Physical row 13 is exactly the selected-support sum after the ordinary
residual tensor. Centering and the output projection are accounted for by
the existing physical kernel identity. -/
theorem physical_thirteen_action_sum (j : Fin 14) (f : AES.WordState → ℝ) :
    action (physicalBlock 13 j) f =
      fun y => ∑ p : SelectedSupport (blockType j).1 (blockType j).2,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y := by
  rw [FourResidualStep.physical_thirteen_kernel, kernelCompose_action,
    ← ResidualIncidenceAggregation.selected_action_sum]
  exact action_fintype_sum residualStepKernel
    (fun p : SelectedSupport (blockType j).1 (blockType j).2 =>
      supportIndexComponent (0 : AES.Word) p.val f)

/-- Exact selected-support aggregation. Input energies are orthogonal;
the sole output loss is the selected-support multiplicity. -/
theorem selected_output_energy (d b : Fin 5) (hdb : d ≤ b)
    (f : AES.WordState → ℝ) :
    (∑ y, (∑ p : SelectedSupport d b,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y) ^ 2) ≤
      graphSquaredBound d b * ∑ x, f x ^ 2 := by
  let n : ℝ := Fintype.card (SelectedSupport d b)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ∑ y, n * ∑ p : SelectedSupport d b,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 :=
      Finset.sum_le_sum (fun y _ => sum_sq_le_card (fun p : SelectedSupport d b =>
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y))
    _ = n * ∑ p : SelectedSupport d b, ∑ y,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ n * ∑ p : SelectedSupport d b,
        ρ ^ (2 * b.val) * κ ^ (4 - b.val) *
          ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hn
      exact Finset.sum_le_sum (fun p _ => selected_piece_energy d b p f)
    _ = (n * ρ ^ (2 * b.val) * κ ^ (4 - b.val)) *
        ∑ p : SelectedSupport d b, ∑ x,
          supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (n * ρ ^ (2 * b.val) * κ ^ (4 - b.val)) * ∑ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact selected_input_energy_le (0 : AES.Word)
        (by rw [AES.word_card]; norm_num) d b f
    _ = graphSquaredBound d b * ∑ x, f x ^ 2 := by
      simp only [n, selectedSupport_card d b hdb, graphSquaredBound]

private theorem blockType_valid : ∀ j : Fin 14,
    (blockType j).1 ≤ (blockType j).2 := by decide

/-- The analytic bound applies to every physical source type. The five
selected columns below meet their frozen scalar caps. -/
theorem physical_thirteen_graph_energy (j : Fin 14) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      graphSquaredBound (blockType j).1 (blockType j).2 * ∑ x, f x ^ 2 := by
  rw [physical_thirteen_action_sum]
  exact selected_output_energy (blockType j).1 (blockType j).2 (blockType_valid j) f

/-- The five frozen caps that meet this ordinary graph coefficient. -/
def ordinaryColumn (j : Fin 14) : Prop :=
  j = 4 ∨ j = 5 ∨ j = 8 ∨ j = 9 ∨ j = 11

instance (j : Fin 14) : Decidable (ordinaryColumn j) := by
  unfold ordinaryColumn
  infer_instance

/-- Exact rational square comparisons follow the analytic argument. -/
theorem certificate_ordinary_bounds (j : Fin 14) (h : ordinaryColumn j) :
    0 ≤ lambda * L 13 j ∧
      graphSquaredBound (blockType j).1 (blockType j).2 ≤ (lambda * L 13 j) ^ 2 := by
  fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | norm_num [graphSquaredBound, ResidualIncidenceCoefficient.multiplicity, Nat.choose, blockType,
        AESRound.Terminal.lambda, AESRound.Certificate.L]

/-- Energy form of each frozen ordinary graph cap. -/
theorem physical_thirteen_energy (j : Fin 14) (h : ordinaryColumn j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      (lambda * L 13 j) ^ 2 * ∑ x, f x ^ 2 :=
  (physical_thirteen_graph_energy j f).trans
    (mul_le_mul_of_nonneg_right (certificate_ordinary_bounds j h).2
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

/--
Physical-kernel norm interface.
-/
theorem physical_thirteen_step_cap (j : Fin 14) (h : ordinaryColumn j) :
    ‖kernelOperator (physicalBlock 13 j)‖ ≤ lambda * L 13 j :=
  kernelOperator_norm_le _ (certificate_ordinary_bounds j h).1 (physical_thirteen_energy j h)

theorem system_thirteen_step_cap (j : Fin 14) (h : ordinaryColumn j) :
    ‖PhysicalProjectionSystem.system.step 13 j‖ ≤ lambda * L 13 j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_thirteen_step_cap j h

theorem physical_thirteen_four_step_cap :
    ‖kernelOperator (physicalBlock 13 4)‖ ≤ lambda * L 13 4 :=
  physical_thirteen_step_cap 4 (by decide)

theorem physical_thirteen_five_step_cap :
    ‖kernelOperator (physicalBlock 13 5)‖ ≤ lambda * L 13 5 :=
  physical_thirteen_step_cap 5 (by decide)

theorem physical_thirteen_eight_step_cap :
    ‖kernelOperator (physicalBlock 13 8)‖ ≤ lambda * L 13 8 :=
  physical_thirteen_step_cap 8 (by decide)

theorem physical_thirteen_nine_step_cap :
    ‖kernelOperator (physicalBlock 13 9)‖ ≤ lambda * L 13 9 :=
  physical_thirteen_step_cap 9 (by decide)

/-- This is a second derivation of the already covered `(13,11)` cap. -/
theorem physical_thirteen_eleven_step_cap :
    ‖kernelOperator (physicalBlock 13 11)‖ ≤ lambda * L 13 11 :=
  physical_thirteen_step_cap 11 (by decide)

end AESConcrete.OrdinaryGraphCaps
