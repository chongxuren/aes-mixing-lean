import AESConcrete.ActivityCodeMoment
import AESConcrete.UniformGraphCaps

/-!
# Activity-only physical energy bounds

A genuine support piece has zero residual degree. Its exact normalized
Boolean expansion is handled by ActivityCodeMoment. Input orthogonality
and one output Cauchy--Schwarz factor give choose(4,b); the certificate
comparison and operator conversion remain in ActivityCodeStepCaps.
Constructive mathematics only; no attacks. The independent retained-key,
whitening, omitted-final-MixColumns, ordered-distinct-pair and 10/14/16
model is unchanged. No complete round theorem is asserted.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityCodeCaps
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.MultiUniformExpansion
open AESConcrete.ActivityCodeScalar
open AESConcrete.ActivityCodeMoment
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.FourResidualStep (residualStepKernel)

set_option maxRecDepth 100000

private theorem mask_zero_of_size_zero :
    ∀ E : Fin 16, maskSize E = 0 → E = 0 := by decide

/-- The zero-degree interface preserves the same signed joint coefficient. -/
theorem multiUniform_energy_of_mask_zero (r E : Fin 16) (hE : maskSize E = 0)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (multiUniform r E h) y ^ 2) ≤
      (numerator (Fintype.card (UniformPositions r E)) ^ 2 /
        (q - 1) ^ Fintype.card (UniformPositions r E)) * ∑ w, h w ^ 2 := by
  have hz := mask_zero_of_size_zero E hE
  subst E
  exact word_multiUniform_activity_energy r h

/-- Each support piece has precisely b nonzero-uniform positions. -/
theorem selected_piece_energy (b : Fin 5) (p : SelectedSupport 0 b)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y ^ 2) ≤
      (numerator b.val ^ 2 / (q - 1) ^ b.val) *
        ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 := by
  obtain ⟨h, _, hc, he⟩ := supportIndexComponent_multi_uniform p.val
    (by rw [AES.word_card]; norm_num) f
  have hzero : maskSize p.val.val.1 = 0 := by simpa using p.val.property.2
  have ht := multiUniform_energy_of_mask_zero p.val.val.2 p.val.val.1 hzero h
  rw [UniformGraphCaps.selected_uniformPositions_card 0 b p] at ht
  simp only [Fin.val_zero, Nat.sub_zero] at ht
  rw [he, hc]
  exact ht

/-- Exactly one support multiplicity is used, on the output sum. -/
theorem selected_output_energy (b : Fin 5) (f : AES.WordState → ℝ) :
    (∑ y, (∑ p : SelectedSupport 0 b,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p.val f) y) ^ 2) ≤
      squaredBound b * ∑ x, f x ^ 2 := by
  have he := UniformGraphCaps.selected_output_energy_of_piece_energy 0 b
    (by omega) (numerator b.val ^ 2 / (q - 1) ^ b.val)
    (div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt q_sub_one_pos) _))
    (fun p g => selected_piece_energy b p g) f
  convert he using 1
  simp only [squaredBound, ResidualIncidenceCoefficient.multiplicity,
    Fin.val_zero, Nat.choose_zero_right, Nat.sub_zero, one_mul]
  ring

/-- The actual physical block, including centering and output projection. -/
theorem physicalBlock_energy (j : Fin 14) (hj : activityColumn j)
    (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 j) f y ^ 2) ≤
      squaredBound (blockType j).2 * ∑ x, f x ^ 2 := by
  rw [OrdinaryGraphCaps.physical_thirteen_action_sum]
  have hz := (activityColumn_blockType j hj).1
  rw [hz]
  exact selected_output_energy (blockType j).2 f

end AESConcrete.ActivityCodeCaps
