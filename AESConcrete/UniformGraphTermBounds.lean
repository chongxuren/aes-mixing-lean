import AESConcrete.GeneralFourierGraphEnergy
import AESConcrete.UniformSelectionCounting
import AESConcrete.UniformGraphScalar

/-!
# Actual ordinary/Fourier bounds for every uniform-subset term

The same arbitrary signed joint residual is used in every term. Ordinary
support geometry and Fourier invariance are separate analytic premises;
the selected term uses one of their actual estimates. Boolean coefficient
grouping is exact, and only odd column-norm powers use the rational scalar
relaxation. No factorization or output orthogonality is assumed.

Constructive bounds only; no attacks, workloads, manuscript or historical
edits, goals or schedules. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and 10/14/16 stay fixed.
Compilation and independent review are required before cap acceptance.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.UniformGraphTermBounds
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.MultiUniformExpansion
open AESConcrete.UniformSelectionCounting
open AESConcrete.UniformGraphScalar
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

/-- The orientation needed by the ordinary union-size identity. -/
theorem residual_disjoint_selectionMask (r E : Fin 16) (σ : Selection r E) :
    MaskDisjoint E (selectionMask r E σ) := by
  intro i hE hU
  exact selectionMask_disjoint r E σ i hU hE

/-- Ordinary support geometry, in the actual residual-step indexing. -/
theorem word_expansionTerm_ordinary_energy (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r E σ h) y ^ 2) ≤
      rho ^ (2 * maskSize (maskUnion E (selectionMask r E σ))) *
        kappa ^ (4 - maskSize (maskUnion E (selectionMask r E σ))) *
          ∑ w, h w ^ 2 := by
  have he := GeneralMDSGraphEnergy.coordinate_supported_energy
    wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    (maskUnion E (selectionMask r E σ)) (maskUnion E (selectionMask r E σ)) rfl
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (21 / 131072 : ℝ) (2 / (15 * 4294967296) : ℝ) (by norm_num)
    (fun _ => SharpDampedWordNorm.word_superbox_residual_energy)
    (fun _ v => le_of_lt (AllColumnBound.actual_word_residual_column_energy_lt v))
    (expansionTerm r E σ h) (expansionTerm_supported r E σ h)
  change (∑ y, action residualTensor
    (fun z => expansionTerm r E σ h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at he
  rw [← NonzeroUniformGraphCap.residualStep_action,
    expansionTerm_energy (by rw [AES.word_card]; norm_num)] at he
  simpa only [rho, kappa] using he

/-- Fourier invariance, in the same actual residual-step indexing. -/
theorem word_expansionTerm_fourier_energy (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r E σ h) y ^ 2) ≤
      rho ^ (2 * (4 - maskSize (selectionMask r E σ))) *
        kappa ^ maskSize (selectionMask r E σ) * ∑ w, h w ^ 2 := by
  have he := GeneralFourierGraphEnergy.word_residual_uniform_mask_energy
    (selectionMask r E σ) (selectionMask r E σ) rfl
    (expansionTerm r E σ h) (expansionTerm_invariant r E σ h)
  change (∑ y, action residualTensor
    (fun z => expansionTerm r E σ h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at he
  rw [← NonzeroUniformGraphCap.residualStep_action,
    expansionTerm_energy (by rw [AES.word_card]; norm_num)] at he
  simpa only [rho, kappa] using he

/-- Choose an actual ordinary or Fourier estimate by its graph dimension.
This proof does not infer either estimate from monotonicity in dimension. -/
theorem word_expansionTerm_graph_energy (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r E σ h) y ^ 2) ≤
      rho ^ (2 * safeGraphDim (maskSize E) (maskSize (selectionMask r E σ))) *
        kappa ^ (4 - safeGraphDim (maskSize E) (maskSize (selectionMask r E σ))) *
          ∑ w, h w ^ 2 := by
  by_cases hc : maskSize E + maskSize (selectionMask r E σ) ≤
      4 - maskSize (selectionMask r E σ)
  · have he := word_expansionTerm_ordinary_energy r E σ h
    rw [maskUnion_size E (selectionMask r E σ)
      (residual_disjoint_selectionMask r E σ)] at he
    simpa only [safeGraphDim, min_eq_left hc] using he
  · have he := word_expansionTerm_fourier_energy r E σ h
    have ht := AESMixing.maskSize_le_four (selectionMask r E σ)
    have hs : 4 - (4 - maskSize (selectionMask r E σ)) =
        maskSize (selectionMask r E σ) := by omega
    have hc' : 4 - maskSize (selectionMask r E σ) ≤
        maskSize E + maskSize (selectionMask r E σ) := by omega
    simpa only [safeGraphDim, min_eq_right hc', hs] using he

/-- The rational norm cap retains all even column-norm powers exactly. -/
theorem word_expansionTerm_safe_energy (r E : Fin 16) (σ : Selection r E)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (expansionTerm r E σ h) y ^ 2) ≤
      safeGraphNorm (safeGraphDim (maskSize E) (maskSize (selectionMask r E σ))) ^ 2 *
        ∑ w, h w ^ 2 := by
  exact (word_expansionTerm_graph_energy r E σ h).trans
    (mul_le_mul_of_nonneg_right
      (graphEnergy_le_safeGraphNorm_sq _ (safeGraphDim_le_four _ _))
      (Finset.sum_nonneg (fun w _ => sq_nonneg (h w))))

private theorem word_sqrt_card : Real.sqrt (Fintype.card AES.Word : ℝ) = 65536 := by
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

/-- Exact size-grouped energy coefficient of a normalized joint residual.
The denominator is squared exactly; no square-root rounding is used. -/
theorem word_multiUniform_energy (r E : Fin 16)
    (h : (MaskCoordinates E → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (multiUniform r E h) y ^ 2) ≤
      (numerator (maskSize E) (Fintype.card (UniformPositions r E)) ^ 2 /
        (4294967295 : ℝ) ^ Fintype.card (UniformPositions r E)) * ∑ w, h w ^ 2 := by
  have hn : 1 < Fintype.card AES.Word := by rw [AES.word_card]; norm_num
  have he := multiUniform_action_energy residualStepKernel hn r E h
    (fun σ => safeGraphNorm (safeGraphDim (maskSize E) (maskSize (selectionMask r E σ))))
    (fun σ => safeGraphNorm_nonneg _)
    (fun σ => word_expansionTerm_safe_energy r E σ h)
  rw [expansion_weighted_sum_by_size hn r E
    (fun t => safeGraphNorm (safeGraphDim (maskSize E) t)), word_sqrt_card] at he
  have hs : (Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) ^
      Fintype.card (UniformPositions r E)) ^ 2 =
        (4294967295 : ℝ) ^ Fintype.card (UniformPositions r E) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by rw [AES.word_card]; norm_num)]
    rw [AES.word_card]
    norm_num
  rw [div_pow, hs] at he
  simpa only [numerator] using he

end AESConcrete.UniformGraphTermBounds
