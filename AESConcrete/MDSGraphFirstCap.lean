import AESConcrete.MDSGraphEnergy
import AESConcrete.FourResidualStep
import AESConcrete.PhysicalProjectionSystem
import AESRound.CertificateData
import AESRound.Terminal

/-!
# graph-column cap for the actual `(13,11)` step

The selected `(3,3)` input projection has four genuine exact-support pieces.
Each piece has one inactive input coordinate and therefore receives the MDS
graph-column energy bound. Their input energies sum to at most the original
energy by the existing support orthogonality theorem. Pointwise Cauchy--
Schwarz, not output orthogonality, aggregates the four outputs.

The actual physical action identity, analytic energy estimate, scalar square
comparison and norm wrapper are separate statements below. No other missing
step cap, return cap or complete AES theorem is
claimed. Independent uniform retained keys, whitening, omitted final
MixColumns, ordered-distinct pairs and the 10/14/16 target stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MDSGraphFirstCap
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.RefinedWordProjection (refinedKernel supportIndexKernel)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

local notation "ρ" => (21 / 131072 : ℝ)
local notation "κ" => (2 / (15 * 4294967296) : ℝ)

/-- Exactly the support indices selected by the actual `(3,3)` projection.
The residual mask and inactive mask retain their existing source meanings. -/
def selectedThree : Finset (SupportIndex 3) :=
  Finset.univ.filter (fun p => maskSize p.val.2 + 3 = 4)

set_option maxRecDepth 100000 in
theorem selectedThree_card : selectedThree.card = 4 := by decide

/-- Every selected piece has a singleton inactive mask. The choice below
uses only nonemptiness of that finite mask, not an input-alphabet search. -/
theorem selectedThree_inactive (p : SupportIndex 3) (hp : p ∈ selectedThree) :
    ∃ r : Fin 4, maskBit p.val.2 r = true := by
  have hselect : maskSize p.val.2 + 3 = 4 := (Finset.mem_filter.mp hp).2
  have hsize : maskSize p.val.2 = 1 := by omega
  have hpos : 0 < (Finset.univ.filter (fun i : Fin 4 => maskBit p.val.2 i)).card := by
    change 0 < maskSize p.val.2
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  exact ⟨r, (Finset.mem_filter.mp hr).2⟩

section InputProjection
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact selected-support expansion of the existing refined projection. -/
theorem refined_three_three_action_sum (z : V) (f : (Fin 4 → V) → ℝ) :
    action (refinedKernel z 3 3) f =
      fun x => ∑ p ∈ selectedThree, supportIndexComponent z p f x := by
  funext y
  unfold action refinedKernel
  -- Normalize both fixed Fin-5 counts before the conditional support sum.
  change (∑ x, (∑ p : SupportIndex 3,
    if maskSize p.val.2 + 3 = 4 then supportIndexKernel z p y x else 0) * f x) =
      ∑ p ∈ selectedThree, supportIndexComponent z p f y
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [selectedThree, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : maskSize p.val.2 + 3 = 4
  · simp only [hp, if_true]
    rfl
  · simp only [hp, if_false, zero_mul, Finset.sum_const_zero]

/-- The selected input energies are bounded using the genuine exact-support
orthogonality and whole-degree contraction. No output statement is involved. -/
theorem selected_input_energy_le (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    (∑ p ∈ selectedThree, ∑ x, supportIndexComponent z p f x ^ 2) ≤
      ∑ x, f x ^ 2 := by
  calc
    (∑ p ∈ selectedThree, ∑ x, supportIndexComponent z p f x ^ 2)
        ≤ ∑ p : SupportIndex 3, ∑ x, supportIndexComponent z p f x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selectedThree)
      intro p _ _
      exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
    _ = ∑ x, degreeComponent z (3 : Fin 5) f x ^ 2 :=
      (supportIndex_degree_energy z hn (3 : Fin 5) f).symm
    _ ≤ ∑ x, f x ^ 2 := degreeComponent_energy_le z hn 3 f

end InputProjection

section FiniteSumAlgebra

private theorem action_finset_sum {I X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (s : Finset I) (f : I → X → ℝ) :
    action K (fun x => ∑ i ∈ s, f i x) =
      fun y => ∑ i ∈ s, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

/-- Four-output aggregation by Cauchy--Schwarz, valid for arbitrary signs.
There is no output-orthogonality hypothesis. -/
theorem selected_sum_sq_le (a : SupportIndex 3 → ℝ) :
    (∑ p ∈ selectedThree, a p) ^ 2 ≤ 4 * ∑ p ∈ selectedThree, a p ^ 2 := by
  -- Normalize the scalar count separately from the real inequality instance.
  have hcount : (∑ _ ∈ selectedThree, (1 : ℝ) ^ 2) = (4 : ℝ) := by
    norm_num [selectedThree_card]
  calc
    (∑ p ∈ selectedThree, a p) ^ 2 =
        (∑ p ∈ selectedThree, (1 : ℝ) * a p) ^ 2 := by simp only [one_mul]
    _ ≤ (∑ _ ∈ selectedThree, (1 : ℝ) ^ 2) *
        ∑ p ∈ selectedThree, a p ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq selectedThree
        (fun _ : SupportIndex 3 => (1 : ℝ)) a
    _ = 4 * ∑ p ∈ selectedThree, a p ^ 2 := by rw [hcount]

end FiniteSumAlgebra

section ActualAction

/-- One selected source piece receives the graph bound in the actual
residual-step indexing. The distinguished output index is chosen as `0`;
the support theorem permits any output index and all output values. -/
theorem selected_piece_energy (p : SupportIndex 3) (hp : p ∈ selectedThree)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2) ≤
      ρ ^ 6 * κ * ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
  obtain ⟨r, hr⟩ := selectedThree_inactive p hp
  have h := MDSGraphEnergy.word_residual_support_piece_energy p r 0 hr f
  change (∑ y, action
    (fun y x => residualTensor y (wordMixAddEquiv.toEquiv x))
    (supportIndexComponent (0 : AES.Word) p f) y ^ 2) ≤ _
  rw [FourResidualStep.input_permutation_action residualTensor wordMixAddEquiv.toEquiv]
  exact h

/-- Exact action of the actual physical `(13,11)` block as the selected
four-piece sum. Centering and the output projection are already accounted
for by the existing `physical_thirteen_kernel` identity. -/
theorem physical_thirteen_eleven_action_sum (f : AES.WordState → ℝ) :
    action (physicalBlock 13 11) f =
      fun y => ∑ p ∈ selectedThree,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y := by
  rw [FourResidualStep.physical_thirteen_kernel, kernelCompose_action]
  change action residualStepKernel (action (refinedKernel (0 : AES.Word) 3 3) f) = _
  rw [refined_three_three_action_sum]
  exact action_finset_sum residualStepKernel selectedThree
    (fun p => supportIndexComponent (0 : AES.Word) p f)

/-- Analytic aggregation of the four selected source pieces. The factor four
comes entirely from output Cauchy--Schwarz; the input sum is orthogonal. -/
theorem selected_output_energy (f : AES.WordState → ℝ) :
    (∑ y, (∑ p ∈ selectedThree,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y) ^ 2) ≤
      4 * ρ ^ 6 * κ * ∑ x, f x ^ 2 := by
  calc
    (∑ y, (∑ p ∈ selectedThree,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y) ^ 2)
        ≤ ∑ y, 4 * ∑ p ∈ selectedThree,
          action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2 :=
      Finset.sum_le_sum (fun y _ => selected_sum_sq_le (fun p =>
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y))
    _ = 4 * ∑ p ∈ selectedThree, ∑ y,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 4 * ∑ p ∈ selectedThree,
        ρ ^ 6 * κ * ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      apply Finset.sum_le_sum
      intro p hp
      exact selected_piece_energy p hp f
    _ = (4 * ρ ^ 6 * κ) *
        ∑ p ∈ selectedThree, ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (4 * ρ ^ 6 * κ) * ∑ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact selected_input_energy_le (0 : AES.Word)
        (by rw [AES.word_card]; norm_num) f
    _ = 4 * ρ ^ 6 * κ * ∑ x, f x ^ 2 := rfl

/-- Actual energy estimate before the frozen numerical square comparison. -/
theorem physical_thirteen_eleven_graph_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 11) f y ^ 2) ≤
      4 * ρ ^ 6 * κ * ∑ x, f x ^ 2 := by
  rw [physical_thirteen_eleven_action_sum]
  exact selected_output_energy f

end ActualAction

section FrozenCap

/-- Exact rational square check, separate from all operator arguments. -/
theorem first_cap_square_le :
    4 * ρ ^ 6 * κ ≤ (lambda * L 13 11) ^ 2 := by
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L]

/--
energy form of the physical `(13,11)` cap.
-/
theorem physical_thirteen_eleven_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 11) f y ^ 2) ≤
      (lambda * L 13 11) ^ 2 * ∑ x, f x ^ 2 := by
  exact (physical_thirteen_eleven_graph_energy f).trans
    (mul_le_mul_of_nonneg_right first_cap_square_le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

/--
actual physical-kernel norm cap.
-/
theorem physical_thirteen_eleven_step_cap :
    ‖kernelOperator (physicalBlock 13 11)‖ ≤ lambda * L 13 11 :=
  kernelOperator_norm_le _
    (by norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L])
    physical_thirteen_eleven_energy

/--
Same cap in the actual projection-system step interface.
-/
theorem system_thirteen_eleven_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 11‖ ≤ lambda * L 13 11 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_thirteen_eleven_step_cap

end FrozenCap
end AESConcrete.MDSGraphFirstCap
