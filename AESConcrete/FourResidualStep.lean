import AESConcrete.RefinedStepZeros
import AESConcrete.FiniteTensorEnergy
import AESConcrete.SharpDampedWordNorm
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Four-residual-word output row and its one sufficient uniform cap

The type (4,4) is certificate index 13. Its exact-support projection is
the whole degree-four projection, hence the tensor of four local word
residual projections. On output this converts the parallel word channel
to four copies of the actual word residual. Global nonzero-uniform
centering is killed by positive degree. Tensor energy, actual word
diffusion reindexing and each refined input projection contraction give
nu^4 for all fourteen input types. This uniform bound meets the frozen
certificate cap only in input column 13; the smaller other entries are
not inferred from it.

No mixed-entry theorem, finite byte cap, return bound or experimental
initialization is a premise. The public root/Audit and certificate data
remain unchanged. Constructive mathematics only; no attacks, local
workloads, manuscript or historical edits. Independent retained keys,
whitening, omitted final MixColumns and ordered distinct pairs stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FourResidualStep
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock refinedCenteredBlock blockType)
open AESConcrete.WordStepZeros (wordStepKernel)
open AESConcrete.CenteredWordStepZeros (centeredWordStepKernel centeredWordStepBlock
  compose_assoc compose_sub_right)
open AESConcrete.DegreeCentering (globalUniformKernel degreeKernel_compose_globalUniformKernel)

private theorem full_degree_index : ∀ a : Fin 4 → Bool,
    degreeIndex a = 4 ↔ a = fun _ => true := by decide

theorem degree_four_tensor {V : Type*} [Fintype V] [DecidableEq V] (z : V) :
    degreeKernel z 4 = coordinateKernel (fun _ : Fin 4 => residualProjection z) := by
  funext y x
  unfold degreeKernel
  simp_rw [full_degree_index]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    productProjection, coordinateKernel, degreePiece]

theorem refined_four_full {V : Type*} [Fintype V] [DecidableEq V] (z : V) :
    refinedKernel z 4 4 = degreeKernel z 4 := by
  have hselect (p : SupportIndex 4) : AES.maskSize p.val.2 + (4 : Fin 5).val = 4 := by
    have hd := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
    have hp := p.property.2
    omega
  calc
    _ = fun y x => ∑ p : SupportIndex 4, supportIndexKernel z p y x := by
      funext y x
      simp only [refinedKernel, hselect, if_true]
      rfl
    _ = _ := supportIndexKernel_sum z 4

theorem pointed_residual_left {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) (z : V) (hD : PointedBistochastic D z) :
    kernelCompose (residualProjection z) D = residualMatrix D z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, residualProjection_action]
  change wordResidual z (action D f) = action (D-activityMatrix z) f
  rw [wordResidual, hD.average_action, kernel_action_sub, activityMatrix_action]

def residualTensor : AES.WordState → AES.WordState → ℝ :=
  coordinateKernel (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)

private theorem parallel_residual_generic {V : Type*} [Fintype V] [DecidableEq V]
    (D : V → V → ℝ) (z : V) (hD : PointedBistochastic D z) :
    kernelCompose (degreeKernel z 4) (coordinateKernel (fun _ : Fin 4 => D)) =
      coordinateKernel (fun _ : Fin 4 => residualMatrix D z) := by
  rw [degree_four_tensor, coordinateKernel_compose]
  congr 1
  funext i
  exact pointed_residual_left D z hD

theorem parallel_four_residual :
    kernelCompose (degreeKernel (0 : AES.Word) 4) AES.parallelSuperboxKernel =
      residualTensor := by
  exact parallel_residual_generic AES.wordSuperboxKernel 0 AES.word_superbox_pointed

def residualStepKernel (y x : AES.WordState) : ℝ :=
  residualTensor y (wordMixAddEquiv x)

-- Keep composition/relabel algebra abstract: concrete AES finite-state
-- reduction during intermediate rewrites otherwise exceeds the worker budget.
private theorem compose_input_generic {V : Type*} [Fintype V]
    (P K : V → V → ℝ) (e : V → V) :
    kernelCompose P (fun y x => K y (e x)) =
      fun y x => kernelCompose P K y (e x) := rfl

private theorem centered_relabel_generic {V : Type*} [Fintype V]
    (P K U R : V → V → ℝ) (e : V → V)
    (hzero : kernelCompose P U = 0) (hres : kernelCompose P K = R) :
    kernelCompose P ((fun y x => K y (e x)) - U) =
      fun y x => R y (e x) := by
  rw [compose_sub_right, hzero, sub_zero, compose_input_generic, hres]

theorem centered_four_residual :
    kernelCompose (degreeKernel (0 : AES.Word) 4) centeredWordStepKernel =
      residualStepKernel := by
  exact centered_relabel_generic (degreeKernel (0 : AES.Word) 4)
    AES.parallelSuperboxKernel (globalUniformKernel (0 : AES.Word))
    residualTensor (fun x => wordMixAddEquiv x)
    (degreeKernel_compose_globalUniformKernel (0 : AES.Word)
      (by rw [AES.word_card]; norm_num) 4 (by decide)) parallel_four_residual

theorem input_permutation_action {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ) (e : Equiv.Perm V) (f : V → ℝ) :
    action (fun y x => K y (e x)) f = action K (fun x => f (e.symm x)) := by
  funext y
  have he := Equiv.sum_comp e (fun x => K y x * f (e.symm x))
  simpa only [action, Equiv.symm_apply_apply] using he

private theorem input_permutation_energy_generic {V : Type*}
    [Fintype V] [DecidableEq V] (K : V → V → ℝ) (e : Equiv.Perm V) (c : ℝ)
    (h : ∀ f, (∑ y, action K f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2)
    (f : V → ℝ) :
    (∑ y, action (fun y x => K y (e x)) f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2 := by
  rw [input_permutation_action]
  have he := h (fun x => f (e.symm x))
  rw [Equiv.sum_comp e.symm (fun x => f x ^ 2)] at he
  exact he

private theorem four_tensor_energy_generic {V : Type*} [Fintype V]
    (D : V → V → ℝ) (ν : ℝ)
    (h : ∀ f, (∑ y, action D f y ^ 2) ≤ ν ^ 2 * ∑ x, f x ^ 2)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => D)) f y ^ 2) ≤
      (ν ^ 4) ^ 2 * ∑ x, f x ^ 2 := by
  have he := FiniteTensorEnergy.uniform_coordinate_energy (I := Fin 4) D ν h f
  simpa only [Fintype.card_fin, ← pow_mul] using he

private theorem degree_sandwich_action_generic {V : Type*}
    [Fintype V] [DecidableEq V] (z : V)
    (S R : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (e : Equiv.Perm (Fin 4 → V))
    (h : kernelCompose (degreeKernel z 4) S = fun y x => R y (e x))
    (f : (Fin 4 → V) → ℝ) :
    action (kernelCompose (degreeKernel z 4)
      (kernelCompose S (degreeKernel z 4))) f =
      action R (fun x => degreeComponent z 4 f (e.symm x)) := by
  rw [compose_assoc, h, kernelCompose_action, input_permutation_action,
    degreeKernel_action]

private theorem degree_sandwich_energy_generic {V : Type*}
    [Fintype V] [DecidableEq V] (z : V) (hn : 1 < Fintype.card V)
    (S R : (Fin 4 → V) → (Fin 4 → V) → ℝ) (c : ℝ)
    (hleft : kernelCompose (degreeKernel z 4) S = R)
    (henergy : ∀ f, (∑ y, action R f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernelCompose (degreeKernel z 4)
      (kernelCompose S (degreeKernel z 4))) f y ^ 2) ≤
      c ^ 2 * ∑ x, f x ^ 2 := by
  rw [compose_assoc, hleft, kernelCompose_action, degreeKernel_action]
  exact (henergy (degreeComponent z 4 f)).trans
    (mul_le_mul_of_nonneg_left (degreeComponent_energy_le z hn 4 f) (sq_nonneg c))

/-- Selecting an orthogonal subfamily of actual support-index projections
is a contraction. This uses the existing support orthogonality and degree
energy identities, without an idempotence premise or a new projection model. -/
theorem refined_energy_le {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (d a : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ x, action (refinedKernel z d a) f x ^ 2) ≤ ∑ x, f x^2 := by
  let selected : SupportIndex d.val → (Fin 4 → V) → ℝ := fun p x =>
    if AES.maskSize p.val.2 + a.val = 4 then supportIndexComponent z p f x else 0
  have hex : action (refinedKernel z d a) f = fun x => ∑ p, selected p x := by
    funext y
    unfold action refinedKernel
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · simp only [hp, if_true, selected]
      rfl
    · simp only [hp, if_false, zero_mul, Finset.sum_const_zero, selected]
  have horth (p q : SupportIndex d.val) (hpq : p ≠ q) :
      (∑ x, selected p x * selected q x) = 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4 <;>
      by_cases hq : AES.maskSize q.val.2 + a.val = 4
    · simp only [selected, hp, hq, if_true]
      exact supportIndex_orthogonal z hn p q hpq f f
    · simp only [selected, hp, hq, if_true, if_false, mul_zero, Finset.sum_const_zero]
    · simp only [selected, hp, hq, if_true, if_false, zero_mul, Finset.sum_const_zero]
    · simp only [selected, hp, hq, if_true, if_false, zero_mul, Finset.sum_const_zero]
  rw [hex, orthogonal_family_energy selected horth]
  calc
    _ ≤ ∑ p : SupportIndex d.val, ∑ x, supportIndexComponent z p f x^2 := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : AES.maskSize p.val.2 + a.val = 4
      · simp only [selected, hp, if_true]
        exact le_rfl
      · simp only [selected, hp, if_false, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero]
        exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
    _ = ∑ x, degreeComponent z d f x^2 := (supportIndex_degree_energy z hn d f).symm
    _ ≤ _ := degreeComponent_energy_le z hn d f

theorem residualStep_energy (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel f y ^ 2) ≤
      ((21/131072 : ℝ)^4)^2 * ∑ x, f x^2 := by
  exact input_permutation_energy_generic residualTensor wordMixAddEquiv.toEquiv
    ((21/131072 : ℝ)^4)
    (four_tensor_energy_generic (residualMatrix AES.wordSuperboxKernel 0)
      (21/131072 : ℝ) SharpDampedWordNorm.word_superbox_residual_energy) f

theorem centered_four_four_action (f : AES.WordState → ℝ) :
    action (centeredWordStepBlock 4 4) f =
      action residualTensor
        (fun x => degreeComponent (0 : AES.Word) 4 f (wordMixAddEquiv.symm x)) := by
  exact degree_sandwich_action_generic (0 : AES.Word) centeredWordStepKernel
    residualTensor wordMixAddEquiv.toEquiv centered_four_residual f

/-- This arbitrary-joint-input energy theorem is at whole-word degree,
not the byte degree used inside the local word-norm proof. -/
theorem centered_four_four_energy (f : AES.WordState → ℝ) :
    (∑ y, action (centeredWordStepBlock 4 4) f y ^ 2) ≤
      ((21/131072 : ℝ)^4)^2 * ∑ x, f x^2 := by
  exact degree_sandwich_energy_generic (0 : AES.Word)
    (by rw [AES.word_card]; norm_num) centeredWordStepKernel residualStepKernel
    ((21/131072 : ℝ)^4) centered_four_residual residualStep_energy f

private theorem refined_four_sandwich_generic {V : Type*}
    [Fintype V] [DecidableEq V] (z : V)
    (S : (Fin 4 → V) → (Fin 4 → V) → ℝ) :
    kernelCompose (refinedKernel z 4 4) (kernelCompose S (refinedKernel z 4 4)) =
      kernelCompose (degreeKernel z 4) (kernelCompose S (degreeKernel z 4)) := by
  rw [refined_four_full]

private theorem refined_four_left_generic {V : Type*}
    [Fintype V] [DecidableEq V] (z : V)
    (S R Q : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (h : kernelCompose (degreeKernel z 4) S = R) :
    kernelCompose (refinedKernel z 4 4) (kernelCompose S Q) = kernelCompose R Q := by
  rw [refined_four_full, compose_assoc, h]

private theorem compose_contraction_energy_generic {V : Type*} [Fintype V]
    (B R P : V → V → ℝ) (c : ℝ) (hblock : B = kernelCompose R P)
    (henergy : ∀ f, (∑ y, action R f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2)
    (hproj : ∀ f, (∑ y, action P f y ^ 2) ≤ ∑ x, f x ^ 2) (f : V → ℝ) :
    (∑ y, action B f y ^ 2) ≤ c ^ 2 * ∑ x, f x ^ 2 := by
  rw [hblock, kernelCompose_action]
  exact (henergy (action P f)).trans
    (mul_le_mul_of_nonneg_left (hproj f) (sq_nonneg c))

theorem physicalBlock_thirteen : physicalBlock 13 13 = centeredWordStepBlock 4 4 := by
  exact refined_four_sandwich_generic (0 : AES.Word) centeredWordStepKernel

theorem physical_thirteen_kernel (j : Fin 14) :
    physicalBlock 13 j = kernelCompose residualStepKernel
      (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2) := by
  exact refined_four_left_generic (0 : AES.Word) centeredWordStepKernel
    residualStepKernel (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2)
    centered_four_residual

theorem physical_thirteen_energy (j : Fin 14) (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      ((21/131072 : ℝ)^4)^2 * ∑ x, f x^2 := by
  exact compose_contraction_energy_generic (physicalBlock 13 j) residualStepKernel
    (refinedKernel (0 : AES.Word) (blockType j).1 (blockType j).2)
    ((21/131072 : ℝ)^4) (physical_thirteen_kernel j) residualStep_energy
    (refined_energy_le (0 : AES.Word) (by rw [AES.word_card]; norm_num)
      (blockType j).1 (blockType j).2) f

/-- The output tensor argument is uniform across input types; it does not
assert any of the smaller certificate caps in columns zero through twelve. -/
theorem physical_thirteen_norm (j : Fin 14) :
    ‖kernelOperator (physicalBlock 13 j)‖ ≤ (21/131072 : ℝ)^4 :=
  kernelOperator_norm_le _ (by positivity) (physical_thirteen_energy j)

theorem physical_thirteen_thirteen_norm :
    ‖kernelOperator (physicalBlock 13 13)‖ ≤ (21/131072 : ℝ)^4 := by
  exact physical_thirteen_norm 13

/-- Exact arithmetic identifies every frozen cap this particular uniform
bound suffices for. Failure of this comparison says nothing negative about
the actual block, whose sharper bounds require additional structure. -/
theorem uniform_row_cap_meets_certificate_iff (j : Fin 14) :
    (21/131072 : ℝ)^4 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L 13 j ↔ j = 13 := by
  fin_cases j <;> norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L] <;> decide

/-- The fixed decimal cap is compared in its actual physical units.
This is arithmetic after the operator theorem, not an operator premise. -/
theorem physical_thirteen_thirteen_step_cap :
    ‖kernelOperator (physicalBlock 13 13)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L 13 13 := by
  apply physical_thirteen_thirteen_norm.trans
  exact (uniform_row_cap_meets_certificate_iff 13).mpr rfl

end AESConcrete.FourResidualStep
