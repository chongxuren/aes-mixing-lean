import AESConcrete.OmittedUniformTwoInputSplit
import AESConcrete.OmittedUniformTwoInputScalar
import AESConcrete.OmittedUniformTwoResponseEnergy

/-!
# response energies for the actual omitted-output (9,6) minor

No desired estimate is a theorem premise. The W estimate is obtained from
exact original-code transports, followed by one generic two- uniform triangle
bound. The W0 estimate is the weighted-line theorem at e=1 on the SAME
normalized original source. The output difference then uses its own sqrt(q-1)
normalizer. The original signed tuple h, including h(0), is common to every
term. A physical factor144 is not silently inserted here.

Fixed constructive AES10/14/16 only.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformTwoInputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport multiplicity)
open AESConcrete.OmittedUniformTwoInputGeometry
open AESConcrete.OmittedUniformTwoInputTransport
open AESConcrete.OmittedUniformTwoInputSplit (extraZeroResponse actualResponse)
open AESConcrete.OmittedUniformTwoInputScalar (normBase normBase_nonneg normBase_sq C)
open AESConcrete.OmittedUniformTwoOutputSplit (zeroCompletion)
open AESConcrete.ActivityCodeScalar (q s s_pos s_sq q_sub_one_pos)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem rawResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  rw [rawResponse_eq_event]
  exact OmittedUniformTwoOutputEventEnergy.single_response_energy pOut (completeInput pIn)
    (completedInactive pIn) h

theorem zeroResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (u : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ v, h v ^ 2 := by
  rw [zeroResponse_eq_event]
  exact OmittedUniformTwoOutputEventEnergy.double_response_energy pOut (completeInput pIn)
    (completedInactive pIn) (completedUniform pIn u) (completedInactive_ne_uniform pIn u) h

theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤
      (((s + 2) * normBase) / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  have hsq : (s * normBase) ^ 2 = q * rho ^ 2 * kappa := by
    rw [mul_pow, normBase_sq, s_sq]
    ring
  have hA : (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn) y ^ 2) ≤
      (s * normBase) ^ 2 * ∑ u, h u ^ 2 := by
    rw [hsq]
    exact rawResponse_energy pOut pIn h
  have hB : (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformFirst pIn).val.val) y ^ 2) ≤
      normBase ^ 2 * ∑ u, h u ^ 2 := by
    rw [normBase_sq]
    exact zeroResponse_energy pOut pIn (uniformFirst pIn) h
  have hC : (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
      normBase ^ 2 * ∑ u, h u ^ 2 := by
    rw [normBase_sq]
    exact zeroResponse_energy pOut pIn (uniformSecond pIn) h
  have hD : (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
      (fun c => c.val (uniformFirst pIn).val.val)
      (fun c => c.val (uniformSecond pIn).val.val) y ^ 2) ≤
      (0 : ℝ) ^ 2 * ∑ u, h u ^ 2 := by
    rw [intersectionResponse_eq_zero pOut pIn _ _ (uniformFirst_ne_second pIn) h]
    simp
  have he := TripleResponse.weightedResponse_energy_le
    (le_of_lt AES.word_card_gt_one)
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c)) (bareKernel pOut pIn)
    (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val) h
    (s * normBase) normBase normBase 0
    (mul_nonneg s_pos.le normBase_nonneg) normBase_nonneg normBase_nonneg (le_refl 0)
    hA hB hC hD
  rw [← inputWeightedResponse_eq_two] at he
  have hnum : s * normBase + normBase + normBase + 0 = (s + 2) * normBase := by ring
  simpa only [hnum, word_card_real, div_pow] using he

theorem extraZeroResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, extraZeroResponse pOut pIn h y ^ 2) ≤
      (normBase / (q - 1)) ^ 2 * ∑ u, h u ^ 2 := by
  rw [OmittedUniformTwoInputSplit.extraZeroResponse_eq_jointResponse]
  have he := WeightedResidualLineCaps.joint_response_energy
    (zeroCompletion pOut) pIn (by decide : 1 ≤ (1 : Fin 5).val) h
  have hcoef : WeightedResidualLineCaps.pieceSquaredBound (1 : Fin 5) =
      (normBase / (q - 1)) ^ 2 := by
    change rho ^ 2 * kappa / (q - 1) ^ 2 = (normBase / (q - 1)) ^ 2
    rw [div_pow, normBase_sq]
  rw [hcoef] at he
  exact he

theorem actualResponse_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  have he := OmittedUniformTwoResponseEnergy.sub_div_energy_le
    (inputWeightedResponse pOut pIn h) (extraZeroResponse pOut pIn h) h
    ((s + 2) * normBase) normBase (q - 1) (Real.sqrt (q - 1))
    (mul_nonneg (by linarith [s_pos]) normBase_nonneg) normBase_nonneg
    q_sub_one_pos.le (Real.sqrt_nonneg _)
    (inputWeightedResponse_energy pOut pIn h) (extraZeroResponse_energy pOut pIn h)
  have hd : (q - 1) ^ 2 * (Real.sqrt (q - 1)) ^ 2 = (q - 1) ^ 3 := by
    rw [Real.sq_sqrt q_sub_one_pos.le]
    ring
  rw [hd, OmittedUniformTwoInputScalar.coefficient_eq] at he
  rw [OmittedUniformTwoInputSplit.actualResponse_eq_split]
  -- The selected minor and retained response count the same finite type.
  have hsum (a b : Fintype (Retained pOut → AES.Word))
      (F : (Retained pOut → AES.Word) → ℝ) :
      (letI := a; ∑ y, F y) = (letI := b; ∑ y, F y) := by
    have hab : a = b := Subsingleton.elim _ _
    cases hab
    rfl
  exact (hsum _ _ (fun y =>
    ((inputWeightedResponse pOut pIn h y - extraZeroResponse pOut pIn h y) /
      Real.sqrt (q - 1)) ^ 2)).le.trans he

-- These are source-text counting proofs, not a physical energy aggregation.
theorem input_multiplicity : ResidualIncidenceCoefficient.multiplicity 1 3 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

theorem output_multiplicity : ResidualIncidenceCoefficient.multiplicity 2 3 = 12 := by
  norm_num [ResidualIncidenceCoefficient.multiplicity, Nat.choose]

end AESConcrete.OmittedUniformTwoInputResponseEnergy
