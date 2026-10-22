import AESConcrete.DirectIncidenceCoefficient
import AESConcrete.ResidualIncidenceStep

/-!
# Nine physical step caps from direct restricted incidence

The actual restricted nonnegative kernel is bounded before residual projection
and selected-support aggregation. The already established support-channel
commutation then damps the same refined intermediate. Frozen scalar
comparisons occur only after that operator proof.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered distinct pairs and 10/14/16 stay fixed. No return, initialization,
experiment or terminal/TV theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DirectIncidenceStep
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.DirectIncidenceCoefficient
open AESConcrete.ResidualIncidenceAggregation (diffusionTransfer)
open AESConcrete.ResidualIncidenceStep (centeredIncidenceBlock centered_incidence_action)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The diffusion and channel estimates apply to the identical projected
intermediate, so their coefficients multiply legitimately. -/
theorem centered_direct_energy (D : V → V → ℝ)
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
      mul_le_mul_of_nonneg_left (refined_diffusion_energy_le L hL hn d a e b hda heb f)
        (sq_nonneg _)
    _ = _ := by ring

/-- Natural family selected by the direct restricted-incidence proof.
It consists of three 2/2, four 2/3 and two 3/3 residual-degree pairs. -/
def directPair (i j : Fin 14) : Prop :=
  ((blockType i).1.val = 2 ∧ (blockType j).1.val = 2 ∧
    (blockType i).2.val + (blockType j).2.val = 6) ∨
  ((blockType i).1.val = 2 ∧ (blockType j).1.val = 3 ∧
    6 ≤ (blockType i).2.val + (blockType j).2.val ∧
    (blockType i).2.val + (blockType j).2.val ≤ 7) ∨
  ((blockType i).1.val = 3 ∧ (blockType j).1.val = 3 ∧
    (blockType i).2.val + (blockType j).2.val = 7)

instance (i j : Fin 14) : Decidable (directPair i j) := by
  unfold directPair
  infer_instance

theorem directPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => directPair ij.1 ij.2)).card = 9 := by decide

private theorem blockType_valid : ∀ i : Fin 14, (blockType i).1 ≤ (blockType i).2 := by decide

private theorem directPair_input_positive : ∀ i j : Fin 14,
    directPair i j → 0 < (blockType j).1.val := by decide

/-- Exact frozen-cap check after the operator argument. No rounded decimal
coefficient or byte-alphabet substitution is used. -/
theorem certificate_direct_bounds (i j : Fin 14) (h : directPair i j) :
    0 ≤ AESRound.Terminal.lambda * AESRound.Certificate.L i j ∧
      ((21/131072 : ℝ) ^ (blockType i).1.val)^2 *
        squaredBound ((2 : ℝ)^32) (blockType i).1 (blockType i).2
          (blockType j).1 (blockType j).2 ≤
            (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | norm_num [squaredBound, rawSquared,
        ResidualIncidenceCoefficient.freeCount, ResidualIncidenceCoefficient.multiplicity,
        Nat.choose, blockType, AESRound.Terminal.lambda, AESRound.Certificate.L]

theorem physical_direct_energy (i j : Fin 14) (h : directPair i j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock i j) f y ^ 2) ≤
      (AESRound.Terminal.lambda * AESRound.Certificate.L i j)^2 * ∑ x, f x ^ 2 := by
  have hcore := centered_direct_energy AES.wordSuperboxKernel
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed (21/131072 : ℝ)
    SharpDampedWordNorm.word_superbox_residual_energy
    (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2
    (blockType_valid i) (blockType_valid j) (directPair_input_positive i j h) f
  change (∑ y, action (physicalBlock i j) f y ^ 2) ≤ _ at hcore
  rw [AES.word_card] at hcore
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hcore
  exact hcore.trans (mul_le_mul_of_nonneg_right (certificate_direct_bounds i j h).2
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem physical_direct_step_cap (i j : Fin 14) (h : directPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j :=
  kernelOperator_norm_le _ (certificate_direct_bounds i j h).1
    (physical_direct_energy i j h)

end AESConcrete.DirectIncidenceStep
