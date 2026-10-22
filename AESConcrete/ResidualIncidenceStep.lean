import AESConcrete.ResidualIncidenceAggregation
import AESConcrete.RefinedChannelCommutation
import AESConcrete.ActivityFull

/-!
# Candidate residual-incidence caps for output degrees zero and one

The diffusion sandwich is first bounded on arbitrary joint functions.
Exact support-channel commutation then permits degree damping on that same
projected output. Only afterwards are the forty-two frozen scalar caps
checked. This separate candidate does not alter the accepted ActivityFull
root or Audit, and proves no return/experiment/full-round theorem.

Constructive mathematics only; no attacks, manuscript or historical edits,
goals, schedules or execution. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered distinct pairs and 10/14/16 stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ResidualIncidenceStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.ResidualIncidenceCoefficient
open AESConcrete.ResidualIncidenceAggregation
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.CenteredWordStepZeros (compose_sub_left)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- This is exactly the physical sandwich, with a generic alphabet/channel. -/
def centeredIncidenceBlock (D : V → V → ℝ) (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (d a e b : Fin 5) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (refinedKernel 0 d a)
    (kernelCompose (DegreeResidualStep.centeredPermutedKernel D 0 L.toEquiv)
      (refinedKernel 0 e b))

theorem centered_incidence_action (D : V → V → ℝ)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D 0)
    (d a e b : Fin 5) (he : e ≠ 0) (f : (Fin 4 → V) → ℝ) :
    action (centeredIncidenceBlock D L d a e b) f =
      action (coordinateKernel (fun _ : Fin 4 => D)) (diffusionTransfer L d a e b f) := by
  unfold centeredIncidenceBlock DegreeResidualStep.centeredPermutedKernel
  rw [compose_sub_left,
    DegreeResidualStep.globalUniformKernel_compose_refined_positive 0 hn e b he, sub_zero,
    kernelCompose_action, kernelCompose_action, FourResidualStep.input_permutation_action]
  unfold diffusionTransfer
  rw [← kernelCompose_action, RefinedChannelCommutation.refined_channel_commutes D 0 hD,
    kernelCompose_action]
  rfl

/-- Incidence and damping multiply on the very same refined intermediate. -/
theorem centered_incidence_energy (D : V → V → ℝ)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (hD : PointedBistochastic D 0) (ν : ℝ)
    (hν : ∀ f, (∑ y, action (residualMatrix D 0) f y ^ 2) ≤
      ν ^ 2 * ∑ x, f x ^ 2)
    (d a e b : Fin 5) (hda : d ≤ a) (heb : e ≤ b) (he : 0 < e.val)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (centeredIncidenceBlock D L d a e b) f y ^ 2) ≤
      (ν ^ d.val)^2 * squaredBound (Fintype.card V) d a e b * ∑ x, f x ^ 2 := by
  have he0 : e ≠ 0 := by
    intro hz
    subst e
    norm_num at he
  simp_rw [centered_incidence_action D L hn hD d a e b he0 f]
  have hcore := RefinedChannelCommutation.refined_damped_energy D 0 hn hD ν hν d a
    (fun y => action (refinedKernel 0 e b) f (L.symm y))
  change (∑ y, action (coordinateKernel (fun _ : Fin 4 => D))
    (diffusionTransfer L d a e b f) y ^ 2) ≤
      (ν ^ d.val)^2 * ∑ x, diffusionTransfer L d a e b f x ^ 2 at hcore
  calc
    _ ≤ (ν ^ d.val)^2 * ∑ x, diffusionTransfer L d a e b f x ^ 2 := hcore
    _ ≤ (ν ^ d.val)^2 *
        (squaredBound (Fintype.card V) d a e b * ∑ x, f x ^ 2) :=
      mul_le_mul_of_nonneg_left (refined_diffusion_energy_le L hL hn d a e b hda heb he f)
        (sq_nonneg _)
    _ = _ := by ring

/-- The new family excludes the known branch/cross zeros and source 13. -/
def incidencePair (i j : Fin 14) : Prop :=
  (blockType i).1.val ≤ 1 ∧
    (0 < (blockType j).1.val ∧ (blockType j).1.val ≤ 3) ∧
    5 ≤ (blockType i).2.val + (blockType j).2.val ∧
    2 ≤ (blockType i).1.val + (blockType j).1.val

instance (i j : Fin 14) : Decidable (incidencePair i j) := by
  unfold incidencePair
  infer_instance

theorem incidencePair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => incidencePair ij.1 ij.2)).card = 42 := by decide

private theorem blockType_valid : ∀ i : Fin 14, (blockType i).1 ≤ (blockType i).2 := by decide

/-- Exact rational screen after the actual operator argument, not a premise. -/
theorem certificate_incidence_bounds (i j : Fin 14) (h : incidencePair i j) :
    0 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L i j ∧
      ((21/131072 : ℝ) ^ (blockType i).1.val)^2 *
        wordSquaredBound (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2 ≤
          (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | norm_num [wordSquaredBound, wordRaw, wordIncidenceTerm, freeCount,
        ResidualIncidenceCoefficient.multiplicity,
        Finset.sum_range_succ, Nat.choose, blockType, AESRound.Terminal.lambda,
        AESRound.Certificate.L]

theorem physical_incidence_energy (i j : Fin 14) (h : incidencePair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 * ∑ x, f x ^ 2 := by
  have hcore := centered_incidence_energy AES.wordSuperboxKernel
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed (21/131072 : ℝ)
    SharpDampedWordNorm.word_superbox_residual_energy
    (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2
    (blockType_valid i) (blockType_valid j) h.2.1.1 f
  change (∑ y, action (physicalBlock i j) f y ^ 2) ≤ _ at hcore
  rw [AES.word_card] at hcore
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hcore
  rw [squaredBound_word] at hcore
  exact hcore.trans (mul_le_mul_of_nonneg_right (certificate_incidence_bounds i j h).2
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem physical_incidence_step_cap (i j : Fin 14) (h : incidencePair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j :=
  kernelOperator_norm_le _ (certificate_incidence_bounds i j h).1
    (physical_incidence_energy i j h)

end AESConcrete.ResidualIncidenceStep
