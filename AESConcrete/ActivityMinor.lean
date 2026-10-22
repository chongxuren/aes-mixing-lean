import AESConcrete.ActivityCode
import AESConcrete.ActivityMinorScalar
import AESConcrete.ActivityMinorGeometry
import AESConcrete.ActivityMinorContraction
import AESConcrete.ActivityMinorMoment
import AESConcrete.ResidualIncidenceAggregation
import AESConcrete.RefinedChannelCommutation

/-! Actual activity-code minor geometry and moment resources.
This root adds no physical/system cap; the accepted inventory remains 149/196.
Constructive mathematics only; no attacks or complete AES10/14/16 claim. -/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinor
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ResidualIncidenceAggregation (selected_action_sum selected_orthogonal)
open AESConcrete.RefinedChannelCommutation (pointed_zero_left pointed_constant_left)
open AESConcrete.FourResidualStep (pointed_residual_left)
open AESConcrete.DegreeCentering (globalUniformKernel degreeKernel_compose_globalUniformKernel)
open AESConcrete.CenteredWordStepZeros
  (centeredWordStepKernel compose_assoc compose_sub_right)
open AESConcrete.RefinedStepZeros (refinedCenteredBlock physicalBlock blockType)
open AESConcrete.WordStepZeros (wordStepKernel wordStepKernel_action)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinorContraction
  (minorResponse nonzeroWeight coordinateKernel_rank_one_minor_energy)
open AESConcrete.NonzeroUniformGraphCap
  (zeroUnit nonzeroUniform zeroUnit_energy nonzeroUniform_energy
    nonzeroConstantMatrix_rank_one)

attribute [local instance] Classical.propDecidable

set_option maxRecDepth 100000

section LocalOutput
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual local channel after selecting its residual, inactive, or active
constant output range. Simultaneously marked and inactive legs are excluded
by the support index's disjoint-mask property. -/
def supportChannelLeg (D : V → V → ℝ) (z : V) (marked inactive : Bool) :
    V → V → ℝ :=
  if marked then residualMatrix D z else
    if inactive then zeroMatrix z else constantMatrix z

theorem supportPiece_channel_left (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (marked inactive : Bool)
    (hlegal : inactive = true → marked ≠ true) :
    kernelCompose (supportPiece z marked inactive) D =
      supportChannelLeg D z marked inactive := by
  cases marked <;> cases inactive
  · exact pointed_constant_left hD
  · exact pointed_zero_left hD
  · exact pointed_residual_left D z hD
  · exact (hlegal rfl rfl).elim

/-- The physical coordinate tensor, with no permutation of its four legs. -/
def supportChannelTensor (D : V → V → ℝ) (z : V) {d : ℕ} (p : SupportIndex d) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  coordinateKernel (fun i =>
    supportChannelLeg D z (AES.maskBit p.val.1 i) (AES.maskBit p.val.2 i))

theorem supportIndex_channel_left (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) {d : ℕ} (p : SupportIndex d) :
    kernelCompose (supportIndexKernel z p) (coordinateKernel (fun _ : Fin 4 => D)) =
      supportChannelTensor D z p := by
  change kernelCompose
      (coordinateKernel (fun i => supportPiece z
        (AES.maskBit p.val.1 i) (AES.maskBit p.val.2 i)))
      (coordinateKernel (fun _ : Fin 4 => D)) = _
  rw [coordinateKernel_compose]
  congr 1
  funext i
  exact supportPiece_channel_left D z hD _ _ (p.property.1 i)

/-- Positive residual degree kills the global centering term even after
the exact active/inactive support refinement. -/
theorem refined_compose_globalUniform_zero (z : V) (hn : 1 < Fintype.card V)
    (d a : Fin 5) (hd : d ≠ 0) :
    kernelCompose (refinedKernel z d a) (globalUniformKernel z) = 0 := by
  calc
    _ = kernelCompose (kernelCompose (refinedKernel z d a) (degreeKernel z d))
        (globalUniformKernel z) := by
      rw [refinedKernel_compose_degreeKernel z hn d a]
    _ = kernelCompose (refinedKernel z d a)
        (kernelCompose (degreeKernel z d) (globalUniformKernel z)) :=
      (compose_assoc _ _ _).symm
    _ = 0 := by
      rw [degreeKernel_compose_globalUniformKernel z hn d hd]
      funext y x
      simp only [kernelCompose, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end LocalOutput

/-- Actual word channels in each selected physical output range. -/
def selectedWordTensor (d a : Fin 5) (p : SelectedSupport d a) :
    AES.WordState → AES.WordState → ℝ :=
  supportChannelTensor AES.wordSuperboxKernel 0 p.val

theorem selected_parallel_word_left (d a : Fin 5) (p : SelectedSupport d a) :
    kernelCompose (supportIndexKernel (0 : AES.Word) p.val) AES.parallelSuperboxKernel =
      selectedWordTensor d a p :=
  supportIndex_channel_left AES.wordSuperboxKernel 0 AES.word_superbox_pointed p.val

theorem refined_centered_word_left (d a : Fin 5) (hd : d ≠ 0) :
    kernelCompose (refinedKernel (0 : AES.Word) d a) centeredWordStepKernel =
      kernelCompose (refinedKernel (0 : AES.Word) d a) wordStepKernel := by
  rw [centeredWordStepKernel, compose_sub_right,
    refined_compose_globalUniform_zero (0 : AES.Word) AES.word_card_gt_one d a hd,
    sub_zero]

theorem positive_refined_block_kernel (d a e b : Fin 5) (hd : d ≠ 0) :
    refinedCenteredBlock d a e b =
      kernelCompose (refinedKernel (0 : AES.Word) d a)
        (kernelCompose wordStepKernel (refinedKernel (0 : AES.Word) e b)) := by
  unfold refinedCenteredBlock
  rw [compose_assoc, refined_centered_word_left d a hd, ← compose_assoc]

/-- Selecting the physical output after the actual raw word step produces
the corresponding residual/zero/constant tensor, after actual diffusion. -/
theorem selected_word_step_action (d a : Fin 5) (p : SelectedSupport d a)
    (g : AES.WordState → ℝ) :
    supportIndexComponent (0 : AES.Word) p.val (action wordStepKernel g) =
      action (selectedWordTensor d a p) (fun x => g (wordMixAddEquiv.symm x)) := by
  rw [wordStepKernel_action]
  change action (supportIndexKernel (0 : AES.Word) p.val)
      (action AES.parallelSuperboxKernel (fun x => g (wordMixAddEquiv.symm x))) = _
  rw [← kernelCompose_action, selected_parallel_word_left d a p]

/-- Exact selected-output decomposition; the input may be an arbitrary joint
real function. The refined input is applied before the actual word step. -/
theorem refined_block_selected_action_sum (d a e b : Fin 5) (hd : d ≠ 0)
    (f : AES.WordState → ℝ) :
    action (refinedCenteredBlock d a e b) f = fun y =>
      ∑ p : SelectedSupport d a, supportIndexComponent (0 : AES.Word) p.val
        (action wordStepKernel (action (refinedKernel (0 : AES.Word) e b) f)) y := by
  rw [positive_refined_block_kernel d a e b hd,
    kernelCompose_action, kernelCompose_action]
  exact (selected_action_sum (0 : AES.Word) d a _).symm

theorem physicalBlock_selected_action_sum (i j : Fin 14)
    (hi : (blockType i).1 ≠ 0) (f : AES.WordState → ℝ) :
    action (physicalBlock i j) f = fun y =>
      ∑ p : SelectedSupport (blockType i).1 (blockType i).2,
        supportIndexComponent (0 : AES.Word) p.val
          (action wordStepKernel
            (action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) f)) y :=
  refined_block_selected_action_sum (blockType i).1 (blockType i).2
    (blockType j).1 (blockType j).2 hi f

/-- Diffusion pullback of the actual refined input; output tensors retain
their original coordinate labels. -/
def physicalInput (j : Fin 14) (f : AES.WordState → ℝ) : AES.WordState → ℝ :=
  fun x => action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2)
    f (wordMixAddEquiv.symm x)

theorem physicalBlock_selected_tensor_action_sum (i j : Fin 14)
    (hi : (blockType i).1 ≠ 0) (f : AES.WordState → ℝ) :
    action (physicalBlock i j) f = fun y =>
      ∑ p : SelectedSupport (blockType i).1 (blockType i).2,
        action (selectedWordTensor (blockType i).1 (blockType i).2 p)
          (physicalInput j f) y := by
  rw [physicalBlock_selected_action_sum i j hi f]
  simp_rw [selected_word_step_action]
  rfl

/-- Distinct selected output pieces remain orthogonal after the entire
word step. Thus their output energies add without output Cauchy--Schwarz. -/
theorem physicalBlock_selected_energy (i j : Fin 14)
    (hi : (blockType i).1 ≠ 0) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) =
      ∑ p : SelectedSupport (blockType i).1 (blockType i).2,
        ∑ y, supportIndexComponent (0 : AES.Word) p.val
          (action wordStepKernel
            (action (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) f)) y ^ 2 := by
  rw [physicalBlock_selected_action_sum i j hi f]
  exact orthogonal_family_energy _ (fun p r hpr =>
    selected_orthogonal (0 : AES.Word) AES.word_card_gt_one
      (blockType i).1 (blockType i).2 p r hpr _ _)

/-- The same exact energy decomposition in the local contraction interface
used by the minor geometry. No scalar cap is asserted. -/
theorem physicalBlock_selected_tensor_energy (i j : Fin 14)
    (hi : (blockType i).1 ≠ 0) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) =
      ∑ p : SelectedSupport (blockType i).1 (blockType i).2,
        ∑ y, action (selectedWordTensor (blockType i).1 (blockType i).2 p)
          (physicalInput j f) y ^ 2 := by
  rw [physicalBlock_selected_energy i j hi f]
  simp_rw [selected_word_step_action]
  rfl

/-- Retained residual labels are exactly the original marked mask. -/
def selectedRetained (d a : Fin 5) (p : SelectedSupport d a) (i : Fin 4) : Prop :=
  AES.maskBit p.val.val.1 i = true

/-- Zero labels are exactly the original inactive mask. -/
def selectedZeros (d a : Fin 5) (p : SelectedSupport d a) (i : Fin 4) : Prop :=
  AES.maskBit p.val.val.2 i = true

theorem zeroMatrix_rank_one {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (y x : V) : zeroMatrix (0 : V) y x = zeroUnit y * zeroUnit x := by
  simp only [zeroMatrix, zeroUnit, supportConstant, if_true]

/-- The selected physical tensor is exactly the rank-one omitted-leg kernel
of the minor contraction interface. The retained predicates preserve the
original four-coordinate labels; no tensor transpose or relabeling occurs. -/
theorem selectedWordTensor_rank_one (d a : Fin 5) (p : SelectedSupport d a) :
    selectedWordTensor d a p = coordinateKernel (fun i =>
      if hi : selectedRetained d a p i then residualMatrix AES.wordSuperboxKernel 0 else
        fun y x => nonzeroWeight (selectedRetained d a p) (selectedZeros d a p) ⟨i, hi⟩ y *
          nonzeroWeight (selectedRetained d a p) (selectedZeros d a p) ⟨i, hi⟩ x) := by
  unfold selectedWordTensor supportChannelTensor
  congr 1
  funext i y x
  by_cases hm : AES.maskBit p.val.val.1 i = true
  · simp [supportChannelLeg, selectedRetained, hm]
  · by_cases hz : AES.maskBit p.val.val.2 i = true
    · simp only [supportChannelLeg, selectedRetained, selectedZeros,
        nonzeroWeight, hm, hz, if_true]
      exact zeroMatrix_rank_one y x
    · simp only [supportChannelLeg, selectedRetained, selectedZeros,
        nonzeroWeight, hm, hz]
      exact nonzeroConstantMatrix_rank_one AES.word_card_gt_one y x

/-- Unit omitted output vectors preserve exactly the actual retained minor
response energy. This identity precedes Boolean expansion or scalar bounds. -/
theorem selectedWordTensor_minor_energy (d a : Fin 5) (p : SelectedSupport d a)
    (f : AES.WordState → ℝ) :
    (∑ y, action (selectedWordTensor d a p) f y ^ 2) =
      ∑ y, minorResponse (selectedRetained d a p)
        (fun _ => residualMatrix AES.wordSuperboxKernel 0)
        (nonzeroWeight (selectedRetained d a p) (selectedZeros d a p)) f y ^ 2 := by
  have hw : ∀ j : {i : Fin 4 // ¬ selectedRetained d a p i},
      (∑ x : AES.Word,
        nonzeroWeight (selectedRetained d a p) (selectedZeros d a p) j x ^ 2) = 1 := by
    intro j
    by_cases hj : selectedZeros d a p j.val
    · simpa only [nonzeroWeight, hj, if_true] using (zeroUnit_energy (V := AES.Word))
    · simpa only [nonzeroWeight, hj, if_false] using
        (nonzeroUniform_energy (V := AES.Word) AES.word_card_gt_one)
  rw [selectedWordTensor_rank_one d a p]
  exact coordinateKernel_rank_one_minor_energy (J := Fin 4) (V := AES.Word)
    (selectedRetained d a p)
    (fun _ : {i : Fin 4 // selectedRetained d a p i} => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained d a p) (selectedZeros d a p)) hw f

end AESConcrete.ActivityMinor
