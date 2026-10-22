import AESConcrete.CoupledPairEventIndexing
import AESConcrete.CoupledPairScalar

/-!
# Actual eight-response energy for the joint residual pair

Each exclusion is matched to the actual source subtype before its bound is
used. The full response and triple intersection both survive. All eight terms
retain one arbitrary signed JOINT amplitude; their norms are added before
squaring. The three physical unit weights are normalized exactly once by
EightResponse.

This establishes a selected response estimate only. Fixed independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct
AES10/14/16 scope and constructive-only research.

Support-component energy transport, physical factor24 and operator conversion
are separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairFiber (ResidualPositions)
open AESConcrete.CoupledPairSource (SourceWord)
open AESConcrete.CoupledPairMinorResponse (residualKernel response rawFull_response_eq)
open AESConcrete.CoupledPairEventIndexing
open AESConcrete.CoupledPairScalar
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q)

variable (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)

/-- The unrestricted full source uses its actual noninjective fiber estimate. -/
theorem raw_full_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤
      (q ^ 3 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  simp_rw [rawFull_response_eq]
  exact CoupledPairFullEnergy.rawFullResponse_energy pIn pOut h

theorem single_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (i : Fin 3) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [zeroResponse_eq pOut pIn h i]
  exact CoupledPairEventEnergy.single_source_response_energy
    (indexedEvents pOut pIn (singleIndexSet i)) (single_indexedEvents_card pOut pIn i) h

theorem pair_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (i j : Fin 3) (hij : i ≠ j) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) (eventValue pOut pIn j) y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [intersectionResponse_eq pOut pIn h i j hij]
  exact CoupledPairEventEnergy.pair_source_response_energy
    (indexedEvents pOut pIn (pairIndexSet i j hij))
    (pair_indexedEvents_card pOut pIn i j hij) h

theorem triple_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, EightResponse.tripleIntersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn 1) (eventValue pOut pIn 2)
      (eventValue pOut pIn 0) y ^ 2) ≤ (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  rw [tripleIntersectionResponse_eq pOut pIn h]
  exact CoupledPairEventEnergy.triple_source_response_energy
    (indexedEvents pOut pIn tripleIndexSet) (triple_indexedEvents_card pOut pIn) h

theorem full_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤ fullNorm ^ 2 * ∑ u, h u ^ 2 := by
  rw [fullNorm_sq]
  exact raw_full_energy pOut pIn h

theorem single_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (i : Fin 3) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) y ^ 2) ≤
      singleNorm ^ 2 * ∑ u, h u ^ 2 :=
  (single_response_energy pOut pIn h i).trans
    (mul_le_mul_of_nonneg_right single_energy_le_singleNorm_sq
      (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

theorem pair_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (i j : Fin 3) (hij : i ≠ j) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn i) (eventValue pOut pIn j) y ^ 2) ≤
      doubleNorm ^ 2 * ∑ u, h u ^ 2 :=
  (pair_response_energy pOut pIn h i j hij).trans
    (mul_le_mul_of_nonneg_right double_energy_le_doubleNorm_sq
      (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

theorem triple_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, EightResponse.tripleIntersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn 1) (eventValue pOut pIn 2)
      (eventValue pOut pIn 0) y ^ 2) ≤ tripleNorm ^ 2 * ∑ u, h u ^ 2 := by
  rw [tripleNorm_sq]
  exact triple_response_energy pOut pIn h

/-- No positivity, vanishing-at-zero, product or fixed-point premise on h. -/
theorem response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ C_safe * ∑ u, h u ^ 2 := by
  have he := EightResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun uv : SourceWord pIn => h uv.1) (residualKernel pOut pIn)
    (eventValue pOut pIn 1) (eventValue pOut pIn 2) (eventValue pOut pIn 0) h
    fullNorm singleNorm doubleNorm tripleNorm
    fullNorm_nonneg singleNorm_nonneg doubleNorm_nonneg tripleNorm_nonneg
    (full_response_safe pOut pIn h)
    (single_response_safe pOut pIn h 1) (single_response_safe pOut pIn h 2)
    (single_response_safe pOut pIn h 0)
    (pair_response_safe pOut pIn h 1 2 (by decide))
    (pair_response_safe pOut pIn h 1 0 (by decide))
    (pair_response_safe pOut pIn h 2 0 (by decide))
    (triple_response_safe pOut pIn h)
  rw [CoupledPairEventGeometry.word_card_real, eight_coefficient_eq] at he
  have h₀ : eventValue pOut pIn 0 = CoupledPairMinorResponse.omittedValue pOut pIn :=
    funext (eventValue_zero pOut pIn)
  have h₁ : eventValue pOut pIn 1 =
      (fun uv : SourceWord pIn => uv.2 (CoupledPairMinorResponse.uniformFirst pIn)) :=
    funext (eventValue_one pOut pIn)
  have h₂ : eventValue pOut pIn 2 =
      (fun uv : SourceWord pIn => uv.2 (CoupledPairMinorResponse.uniformSecond pIn)) :=
    funext (eventValue_two pOut pIn)
  rw [h₀, h₁, h₂] at he
  exact he

end AESConcrete.CoupledPairResponseEnergy
