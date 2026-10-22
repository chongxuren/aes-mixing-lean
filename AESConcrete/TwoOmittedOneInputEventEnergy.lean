import AESConcrete.TwoOmittedOneInputEventResponses
import AESConcrete.FiniteTensorEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Ordinary tensor estimates on the genuine restricted sources for (10,12)

The two q-fiber maps use the included generic finite Cauchy helper. The
double-zero retained map is genuinely injective and its J source energy is a
sub-sum, not a new H. All kernels and amplitudes are signed/joint; no product-
input hypothesis. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputEvents
open AESConcrete.TwoOmittedOneInputSource
open AESConcrete.TwoOmittedOneInputEventResponses
open AESConcrete.InvariantSubspaceEnergy (zeroExtend)
open AESConcrete.UniformGraphScalar (rho)
open AESConcrete.ActivityCodeScalar (q q_pos)
open AESConcrete.TwoOmittedOneInputScalar (D D_pos)
open AESConcrete.DoubleUniformFourierEnergy (word_card_real)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem ordinary_tensor_energy (pOut : SelectedSupport 2 4)
    (f : (Retained pOut → AES.Word) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Retained pOut =>
      residualMatrix AES.wordSuperboxKernel 0)) f y ^ 2) ≤ rho ^ 4 * ∑ x, f x ^ 2 := by
  have he := FiniteTensorEnergy.uniform_coordinate_energy
    (I := Retained pOut) (residualMatrix AES.wordSuperboxKernel 0) rho
    SharpDampedWordNorm.word_superbox_residual_energy f
  rw [retained_card] at he
  simpa only [show 2 * 2 = 4 by decide] using he

/-- Generic q-fiber response bound, with the entire source energy exposed. -/
theorem fiber_response_energy {S : Type} [Fintype S] (pOut : SelectedSupport 2 4)
    (E : S → Retained pOut → AES.Word) (e : S ≃ AES.Word × (Retained pOut → AES.Word))
    (hE : ∀ c, (e c).2 = E c) (mu : S → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) E mu y ^ 2) ≤
      (q * rho ^ 4) * ∑ c, mu c ^ 2 := by
  have hp := OmittedUniformTwoInputPushforward.pushforward_energy_le E e hE mu
  rw [word_card_real] at hp
  simp_rw [InvariantSubspaceEnergy.response_eq_action]
  exact (ordinary_tensor_energy pOut (zeroExtend E mu)).trans
    ((mul_le_mul_of_nonneg_left hp (pow_nonneg (UniformGraphScalar.rho_nonneg) _)).trans_eq
      (by ring))

theorem inputZero_amplitude_energy (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : InputZero pIn, psi pIn h c.val ^ 2) = ∑ r, h r ^ 2 :=
  (inputZeroResidualEquiv pIn).sum_comp (fun r => h r ^ 2)

theorem singleZero_amplitude_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : SingleZero pOut a, psi pIn h c.val ^ 2) = ∑ r, h r ^ 2 :=
  (singleZeroResidualEquiv pOut pIn a).sum_comp (fun r => h r ^ 2)

theorem doubleZero_amplitude_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : DoubleZero pOut, psi pIn h c.val ^ 2) ≤ ∑ r, h r ^ 2 :=
  IndexedTripleEnergy.restriction_energy_le (fun c : DoubleZero pOut => residualTuple pIn c.val)
    (doubleZeroResidual_injective pOut pIn) h

/-- Pointwise input U bound on any restriction; original G is unchanged. -/
theorem restricted_source_energy {S : Type} [Fintype S]
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ)
    (v : S → AES.WordState) :
    (∑ c, normalizedSource pIn h (v c) ^ 2) ≤
      (∑ c, psi pIn h (v c) ^ 2) / D := by
  simp_rw [normalizedSource_eq, mul_pow]
  calc
    _ ≤ ∑ c, psi pIn h (v c) ^ 2 * (1 / D) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (nonzeroUniform_sq_le _) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem singleZero_source_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : SingleZero pOut a, normalizedSource pIn h c.val ^ 2) ≤ (∑ r, h r ^ 2) / D := by
  have he := restricted_source_energy pIn h (fun c : SingleZero pOut a => c.val)
  rw [singleZero_amplitude_energy pOut pIn a h] at he
  exact he

theorem doubleZero_source_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : DoubleZero pOut, normalizedSource pIn h c.val ^ 2) ≤ (∑ r, h r ^ 2) / D :=
  (restricted_source_energy pIn h (fun c : DoubleZero pOut => c.val)).trans
    (div_le_div_of_nonneg_right (doubleZero_amplitude_energy pOut pIn h) D_pos.le)

theorem inputZeroResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, inputZeroResponse pOut pIn h y ^ 2) ≤ (q * rho ^ 4) * ∑ r, h r ^ 2 := by
  rw [inputZeroResponse_eq_domain]
  have he := fiber_response_energy pOut _ (inputZeroFiberParam pOut pIn (residualFirst pIn))
    (inputZeroFiberParam_snd pOut pIn (residualFirst pIn))
    (fun c : InputZero pIn => psi pIn h c.val)
  rw [inputZero_amplitude_energy pIn h] at he
  exact he

theorem singleConditionalResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, singleConditionalResponse pOut pIn a h y ^ 2) ≤
      (q * rho ^ 4 / D) * ∑ r, h r ^ 2 := by
  rw [singleConditionalResponse_eq_domain]
  have he := fiber_response_energy pOut _ (singleZeroFiberParam pOut pIn a (residualFirst pIn))
    (singleZeroFiberParam_snd pOut pIn a (residualFirst pIn))
    (fun c : SingleZero pOut a => normalizedSource pIn h c.val)
  exact he.trans ((mul_le_mul_of_nonneg_left (singleZero_source_energy pOut pIn a h)
    (mul_nonneg q_pos.le (pow_nonneg UniformGraphScalar.rho_nonneg _))).trans_eq (by ring))

theorem doubleConditionalResponse_energy (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, doubleConditionalResponse pOut pIn h y ^ 2) ≤
      (rho ^ 4 / D) * ∑ r, h r ^ 2 := by
  rw [doubleConditionalResponse_eq_domain]
  let E := eventRetained pOut (maskComplement pOut.val.val.1) 0
  let mu := fun c : DoubleZero pOut => normalizedSource pIn h c.val
  have hi : Function.Injective E := (doubleZeroRetainedEquiv pOut).injective
  have hp := InvariantSubspaceEnergy.zeroExtend_energy E hi mu
  have he := ordinary_tensor_energy pOut (zeroExtend E mu)
  rw [hp] at he
  change (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) E mu y ^ 2) ≤ _
  simp_rw [InvariantSubspaceEnergy.response_eq_action]
  exact he.trans ((mul_le_mul_of_nonneg_left (doubleZero_source_energy pOut pIn h)
    (pow_nonneg UniformGraphScalar.rho_nonneg _)).trans_eq (by ring))

end AESConcrete.TwoOmittedOneInputEventEnergy
