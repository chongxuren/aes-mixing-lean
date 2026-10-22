import AESConcrete.TwoOmittedOneInputFullEnergy
import AESConcrete.TwoOmittedOneInputEventEnergy
import AESConcrete.TwoOmittedOneInputSplit

/-!
# Same-source L2 composition for (10,12)

Norms add before squaring, without orthogonality between output-zero events.
The same arbitrary signed joint h, including h(0), is used in A0, Au and all
four W terms. Exact denominator D*sqrt(D) and N=s*q*rho*eta+(3s+1)*rho^2 give
C=N^2/D^3. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputSource
open AESConcrete.TwoOmittedOneInputEventResponses
open AESConcrete.TwoOmittedOneInputSplit (actualResponse actualResponse_eq_split)
open AESConcrete.TwoOmittedOneInputScalar

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

/-- Generic signed subtraction; a and b are proven component norm coefficients. -/
theorem sub_div_energy_le {Y Z : Type} [Fintype Y] [Fintype Z]
    (A B : Y → ℝ) (g : Z → ℝ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hA : (∑ y, A y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, B y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, ((A y - B y) / c) ^ 2) ≤ ((a + b) / c) ^ 2 * ∑ z, g z ^ 2 := by
  have hcoef : 0 ≤ (a + b) / c := div_nonneg (add_nonneg ha hb) hc.le
  have ht : l2 (fun y => (A y - B y) / c) ≤ ((a + b) / c) * l2 g := by
    rw [WeightedResponse.l2_div, abs_of_pos hc]
    calc
      _ ≤ (l2 A + l2 B) / c := div_le_div_of_nonneg_right
        (WeightedResponse.l2_sub_le A B) hc.le
      _ ≤ (a * l2 g + b * l2 g) / c := div_le_div_of_nonneg_right
        (add_le_add (l2_le_of_energy A g a ha hA) (l2_le_of_energy B g b hb hB)) hc.le
      _ = _ := by ring
  have hs := (sq_le_sq₀ (l2_nonneg (fun y => (A y - B y) / c))
    (mul_nonneg hcoef (l2_nonneg g))).mpr ht
  simpa only [mul_pow, l2_sq] using hs

theorem rawResponse_norm_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤ fullRawNorm ^ 2 * ∑ r, h r ^ 2 :=
  (TwoOmittedOneInputFullEnergy.rawResponse_energy pOut pIn h).trans
    (mul_le_mul_of_nonneg_right full_energy_coefficient_le
      (Finset.sum_nonneg (fun r _ => sq_nonneg (h r))))

theorem inputZeroResponse_norm_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputZeroResponse pOut pIn h y ^ 2) ≤ inputZeroNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [inputZeroNorm_sq]
  exact TwoOmittedOneInputEventEnergy.inputZeroResponse_energy pOut pIn h

theorem inputWeightedResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputWeightedResponse pOut pIn h y ^ 2) ≤ inputNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [inputWeightedResponse_eq_split]
  exact sub_div_energy_le (rawResponse pOut pIn h) (inputZeroResponse pOut pIn h) h
    fullRawNorm inputZeroNorm d fullRawNorm_nonneg inputZeroNorm_nonneg d_pos
    (rawResponse_norm_energy pOut pIn h) (inputZeroResponse_norm_energy pOut pIn h)

theorem singleConditionalResponse_norm_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, singleConditionalResponse pOut pIn a h y ^ 2) ≤ singleNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [singleNorm_sq]
  exact TwoOmittedOneInputEventEnergy.singleConditionalResponse_energy pOut pIn a h

theorem doubleConditionalResponse_norm_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, doubleConditionalResponse pOut pIn h y ^ 2) ≤ doubleNorm ^ 2 * ∑ r, h r ^ 2 := by
  rw [doubleNorm_sq]
  exact TwoOmittedOneInputEventEnergy.doubleConditionalResponse_energy pOut pIn h

/-- Unconditional actual response bound: no desired-bound premise occurs. -/
theorem actualResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, actualResponse pOut pIn h y ^ 2) ≤ C * ∑ r, h r ^ 2 := by
  let A := inputWeightedResponse pOut pIn h
  let B := singleConditionalResponse pOut pIn (omittedFirst pOut) h
  let B' := singleConditionalResponse pOut pIn (omittedSecond pOut) h
  let E := doubleConditionalResponse pOut pIn h
  have ht := TripleResponse.four_response_l2_le A B B' E h
    inputNorm singleNorm singleNorm doubleNorm D
    inputNorm_nonneg singleNorm_nonneg singleNorm_nonneg doubleNorm_nonneg
    (inputWeightedResponse_energy pOut pIn h)
    (singleConditionalResponse_norm_energy pOut pIn (omittedFirst pOut) h)
    (singleConditionalResponse_norm_energy pOut pIn (omittedSecond pOut) h)
    (doubleConditionalResponse_norm_energy pOut pIn h)
  rw [abs_of_pos D_pos] at ht
  have hc : 0 ≤ (inputNorm + singleNorm + singleNorm + doubleNorm) / D :=
    div_nonneg (by linarith [inputNorm_nonneg, singleNorm_nonneg, doubleNorm_nonneg]) D_pos.le
  have hs := (sq_le_sq₀ (l2_nonneg (fun y => (A y - B y - B' y + E y) / D))
    (mul_nonneg hc (l2_nonneg h))).mpr ht
  simp only [mul_pow, l2_sq, combined_coefficient] at hs
  rw [actualResponse_eq_split]
  calc
    _ = ∑ y : Retained pOut → AES.Word, ((A y - B y - B' y + E y) / D) ^ 2 :=
      counting_sum_instances _ _ _
    _ ≤ _ := hs

end AESConcrete.TwoOmittedOneInputResponseEnergy
