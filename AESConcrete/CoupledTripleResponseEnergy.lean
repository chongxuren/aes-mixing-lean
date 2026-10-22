import AESConcrete.CoupledTripleEventIndexing
import AESConcrete.CoupledTripleScalar

/-!
# Four-response energy assembly for an arbitrary joint residual triple

The raw full source has coefficient q^2*rho^4*kappa. The ORIGINAL scalar-input
and omitted-output exclusions each have rho^6; their surviving plane has
rho^4*kappa. All four bounds concern the same arbitrary signed JOINT h on the
whole original residual triple. Its lift to the full scalar source is separate
from the comparator h in TripleResponse.weightedResponse_energy_le.

One nonnegative square-root witness supplies the existing scalar norm caps.
All four norms are added before squaring, with exactly the two unit weights'
energy denominator (q-1)^2. Neither endpoint is discarded; no response
orthogonality, factorization, axis-zero, positivity or cancellation is
assumed. The final selected-response coefficient is CoupledTripleScalar.C3.
Actual support-component transport, physical factor16, certificate/operator
integration remain separate.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber (ResidualPositions)
open AESConcrete.CoupledTripleSource (SourceWord)
open AESConcrete.CoupledTripleMinorResponse (residualKernel response rawFull_response_eq)
open AESConcrete.CoupledTripleEventIndexing
open AESConcrete.CoupledTripleScalar
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q)

/-- A scalar witness only; it imposes no condition on the joint amplitude. -/
def normBase : ℝ := Real.sqrt baseSquared

theorem normBase_nonneg : 0 ≤ normBase := Real.sqrt_nonneg _

theorem normBase_sq : normBase ^ 2 = baseSquared := Real.sq_sqrt baseSquared_nonneg

variable (pOut pIn : SelectedSupport 3 4)

/-- The unrestricted full source retains its actual noninjective-fiber bound. -/
theorem raw_full_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤
      (q ^ 2 * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  simp_rw [rawFull_response_eq]
  exact CoupledTripleFullEnergy.rawFullResponse_energy pIn pOut h

theorem input_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2) y ^ 2) ≤
      rho ^ 6 * ∑ u, h u ^ 2 := by
  rw [input_zeroResponse_eq pOut pIn h]
  exact CoupledTripleEventEnergy.input_event_energy (pOut := pOut) (pIn := pIn) h

theorem output_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (CoupledTripleMinorResponse.omittedValue pOut pIn) y ^ 2) ≤
      rho ^ 6 * ∑ u, h u ^ 2 := by
  rw [output_zeroResponse_eq pOut pIn h]
  exact CoupledTripleEventEnergy.output_event_energy (pOut := pOut) (pIn := pIn) h

theorem intersection_response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2)
      (CoupledTripleMinorResponse.omittedValue pOut pIn) y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [intersectionResponse_eq pOut pIn h]
  exact CoupledTripleEventEnergy.intersection_event_energy (pOut := pOut) (pIn := pIn) h

theorem full_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) y ^ 2) ≤ fullNorm normBase ^ 2 * ∑ u, h u ^ 2 := by
  rw [fullNorm_sq normBase normBase_sq]
  exact raw_full_energy pOut pIn h

theorem input_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2) y ^ 2) ≤
      singleNorm normBase ^ 2 * ∑ u, h u ^ 2 :=
  (input_response_energy pOut pIn h).trans
    (mul_le_mul_of_nonneg_right (single_energy_le_singleNorm_sq normBase normBase_sq)
      (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

theorem output_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (CoupledTripleMinorResponse.omittedValue pOut pIn) y ^ 2) ≤
      singleNorm normBase ^ 2 * ∑ u, h u ^ 2 :=
  (output_response_energy pOut pIn h).trans
    (mul_le_mul_of_nonneg_right (single_energy_le_singleNorm_sq normBase normBase_sq)
      (Finset.sum_nonneg (fun u _ => sq_nonneg (h u))))

theorem intersection_response_safe (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (fun uv => uv.2)
      (CoupledTripleMinorResponse.omittedValue pOut pIn) y ^ 2) ≤
      intersectionNorm normBase ^ 2 * ∑ u, h u ^ 2 := by
  rw [intersectionNorm_sq normBase normBase_sq]
  exact intersection_response_energy pOut pIn h

/-- Add all four norms before squaring, against the same original signed h. -/
theorem response_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ C3 * ∑ u, h u ^ 2 := by
  have he := TripleResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun uv : SourceWord pIn => h uv.1) (residualKernel pOut pIn)
    (fun uv => uv.2) (CoupledTripleMinorResponse.omittedValue pOut pIn) h
    (fullNorm normBase) (singleNorm normBase) (singleNorm normBase) (intersectionNorm normBase)
    (fullNorm_nonneg normBase normBase_nonneg)
    (singleNorm_nonneg normBase normBase_nonneg)
    (singleNorm_nonneg normBase normBase_nonneg)
    (intersectionNorm_nonneg normBase normBase_nonneg)
    (full_response_safe pOut pIn h)
    (input_response_safe pOut pIn h) (output_response_safe pOut pIn h)
    (intersection_response_safe pOut pIn h)
  rw [DoubleUniformFourierEnergy.word_card_real, four_coefficient_eq normBase normBase_sq] at he
  exact he

end AESConcrete.CoupledTripleResponseEnergy
