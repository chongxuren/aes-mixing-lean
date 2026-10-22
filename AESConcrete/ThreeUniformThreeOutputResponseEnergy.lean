import AESConcrete.ThreeUniformThreeOutputFullEnergy
import AESConcrete.ThreeUniformThreeOutputEventEnergy
import AESConcrete.ThreeUniformThreeOutputScalar
import AESConcrete.WeightedThreeOutputCaps
import AESConcrete.SevenResponse

/-!
# Seven responses on the actual three-output code

Candidate (11,7). Each of the three original input uniforms occurs once.
The full response, three zero planes, and three pair intersections all retain
the same arbitrary signed residual-singleton amplitude, including h(0).
The triple intersection kills the actual kernel. Norms are added before
squaring; normalization is exactly (q-1)^3 in the energy coefficient.
Constructive fixed AES10/14/16 independent retained keys, whitening, omitted
final MixColumns, ordered-distinct reference; no attacks or manuscript edits.
Compilation and independent review remain separate from source authoring.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ThreeUniformThreeOutputResponseEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeUniformThreeOutputGeometry
open AESConcrete.ThreeUniformThreeOutputScalar
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def uniformIndexEquiv (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn ≃ Fin 3 :=
  Fintype.equivOfCardEq (by rw [sourceUniformPositions_card]; simp)

def uniformFirst (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 0

def uniformSecond (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 1

def uniformThird (pIn : SelectedSupport 1 4) : SourceUniformPositions pIn :=
  (uniformIndexEquiv pIn).symm 2

theorem uniformFirst_ne_second (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformSecond pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniformFirst_ne_third (pIn : SelectedSupport 1 4) :
    uniformFirst pIn ≠ uniformThird pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniformSecond_ne_third (pIn : SelectedSupport 1 4) :
    uniformSecond pIn ≠ uniformThird pIn :=
  (uniformIndexEquiv pIn).symm.injective.ne (by decide)

theorem uniform_product (pIn : SelectedSupport 1 4) (x : AES.WordState) :
    WeightedThreeOutputCaps.uniformWeight pIn x =
      nonzeroUniform (x (uniformFirst pIn).val.val) *
        nonzeroUniform (x (uniformSecond pIn).val.val) *
          nonzeroUniform (x (uniformThird pIn).val.val) := by
  have hp := (uniformIndexEquiv pIn).symm.prod_comp
    (fun j : SourceUniformPositions pIn => nonzeroUniform (x j.val.val))
  simpa only [WeightedThreeOutputCaps.uniformWeight, Fin.prod_univ_three,
    uniformFirst, uniformSecond, uniformThird, mul_assoc] using hp.symm

def residualKernel (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i)
      (AESConcrete.WordCrossZero.wordMixAddEquiv c.val i.val)

def response (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  WeightedResponse.weightedResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (residualKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val)
    (fun c => c.val (uniformThird pIn).val.val)

theorem jointResponse_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedThreeOutputCaps.jointResponse pOut pIn h = response pOut pIn h := by
  funext y
  unfold WeightedThreeOutputCaps.jointResponse IndexedTripleEnergy.response
    response WeightedResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro c _
  rw [WeightedThreeOutputCaps.weightedAmplitude, uniform_product]
  change h (residualTuple pOut pIn c) *
    (nonzeroUniform (c.val (uniformFirst pIn).val.val) *
      nonzeroUniform (c.val (uniformSecond pIn).val.val) *
        nonzeroUniform (c.val (uniformThird pIn).val.val)) * residualKernel pOut pIn y c = _
  ring

theorem rawFull_response_eq (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    WeightedResponse.rawResponse (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) =
        ThreeUniformThreeOutputFullEnergy.rawFullResponse pOut pIn h := rfl

variable (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)

theorem full_response_safe (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.rawResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) y ^ 2) ≤ fullNorm ^ 2 * ∑ u, h u ^ 2 := by
  rw [rawFull_response_eq, fullNorm_sq]
  exact ThreeUniformThreeOutputFullEnergy.rawFullResponse_energy pOut pIn h

theorem single_response_safe (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
        singleNorm ^ 2 * ∑ v, h v ^ 2 :=
  (ThreeUniformThreeOutputEventEnergy.single_zeroResponse_energy pOut pIn u h).trans
    (mul_le_mul_of_nonneg_right single_energy_le_singleNorm_sq
      (Finset.sum_nonneg (fun v _ => sq_nonneg (h v))))

theorem double_response_safe (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (residualKernel pOut pIn) (fun c => c.val u.val.val)
      (fun c => c.val v.val.val) y ^ 2) ≤ doubleNorm ^ 2 * ∑ x, h x ^ 2 := by
  rw [doubleNorm_sq]
  exact ThreeUniformThreeOutputEventEnergy.double_intersectionResponse_energy
    pOut pIn u v huv h

theorem triple_zero_kernel (y : Retained pOut → AES.Word) (c : Code pOut pIn)
    (h₀ : c.val (uniformFirst pIn).val.val = 0)
    (h₁ : c.val (uniformSecond pIn).val.val = 0)
    (h₂ : c.val (uniformThird pIn).val.val = 0) : residualKernel pOut pIn y c = 0 :=
  ThreeUniformThreeOutputEventEnergy.triple_zero_kernel pOut pIn
    (uniformFirst pIn) (uniformSecond pIn) (uniformThird pIn)
    (uniformFirst_ne_second pIn) (uniformFirst_ne_third pIn)
    (uniformSecond_ne_third pIn) y c h₀ h₁ h₂

/-- Seven original responses, one source energy, and three normalizing weights. -/
theorem response_energy (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  have he := SevenResponse.weightedResponse_energy_le (le_of_lt AES.word_card_gt_one)
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
    (residualKernel pOut pIn) (fun c => c.val (uniformFirst pIn).val.val)
    (fun c => c.val (uniformSecond pIn).val.val)
    (fun c => c.val (uniformThird pIn).val.val) h
    (triple_zero_kernel pOut pIn)
    fullNorm singleNorm doubleNorm fullNorm_nonneg singleNorm_nonneg doubleNorm_nonneg
    (full_response_safe pOut pIn h)
    (single_response_safe pOut pIn (uniformFirst pIn) h)
    (single_response_safe pOut pIn (uniformSecond pIn) h)
    (single_response_safe pOut pIn (uniformThird pIn) h)
    (double_response_safe pOut pIn (uniformFirst pIn) (uniformSecond pIn)
      (uniformFirst_ne_second pIn) h)
    (double_response_safe pOut pIn (uniformFirst pIn) (uniformThird pIn)
      (uniformFirst_ne_third pIn) h)
    (double_response_safe pOut pIn (uniformSecond pIn) (uniformThird pIn)
      (uniformSecond_ne_third pIn) h)
  rw [DoubleUniformFourierEnergy.word_card_real, seven_coefficient_eq] at he
  exact he

theorem joint_response_energy (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedThreeOutputCaps.jointResponse pOut pIn h y ^ 2) ≤ C * ∑ u, h u ^ 2 := by
  rw [jointResponse_eq]
  exact response_energy pOut pIn h

end AESConcrete.ThreeUniformThreeOutputResponseEnergy
