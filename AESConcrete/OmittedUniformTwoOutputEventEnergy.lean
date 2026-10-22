import AESConcrete.OmittedUniformTwoOutputEventGeometry
import AESConcrete.DoubleUniformFourierEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound

/-!
# Two-output energy for actual original input-zero events

A single-zero plane has an injective actual retained image and residual-zero
translation line surjective onto the one dependent output. The generic Fourier
theorem gives rho^2*kappa times its original source energy q*sum h^2. A double-zero
line is an ordinary graph over one retained output; its original residual
singleton parametrizes it exactly, giving rho^2*kappa times sum h^2. The same
arbitrary signed original tuple h, including h(0), is used throughout. No
three-output coefficient is substituted.

The triple-input-zero kernel vanishes because actual MDS forces physical zero
and the residual kernel has a zero column. Bare full-response cancellation is
handled by the sibling BareResponse module. Weighted-response, selected-minor
and physical-cap bounds are separate.

Constructive fixed AES10/14/16; independent retained keys, whitening, omitted
final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoOutputEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoOutputGeometry
open AESConcrete.OmittedUniformTwoOutputBareResponse (bareKernel)
open AESConcrete.OmittedUniformTwoOutputEventGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy
  (word_card_real word_fourier_operator_energy word_fourier_column_energy)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- One free Fourier operator factor and one dependent column factor. -/
theorem single_response_energy_at (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn) (s : Retained pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (singleMask u) h y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
    freeCoordinates_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
    dependentCoordinates_card pOut s
  have henergy : (∑ c : EventCode pOut pIn (singleMask u),
      h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2) = q * ∑ x, h x ^ 2 := by
    rw [single_amplitude_energy pOut pIn u h, word_card_real]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : Retained pOut => i ≠ s) rho kappa kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy
    (singleRetainedHom pOut pIn u) (single_retained_bijective pOut pIn u).1
    (singleTranslation pOut pIn u) (single_translation_dependent_surjective pOut pIn u s)
    (fun c => h (eventResidualTuple pOut pIn (singleMask u) c))
    (single_amplitude_translation pOut pIn u h)
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, henergy] at he
  exact he.trans_eq (by ring)

theorem single_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (singleMask u) h y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact single_response_energy_at pOut pIn u (Classical.choice inferInstance) h

/-- The actual double-zero line is a graph over any retained singleton. -/
theorem double_code_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (mu : EventCode pOut pIn (doubleMask u v) → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (eventCurve pOut pIn (doubleMask u v)) mu y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ c, mu c ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤
        rho ^ 2 * ∑ x, g x ^ 2 := SharpDampedWordNorm.word_superbox_residual_energy
  have hc : ∀ v : AES.Word,
      (∑ y, residualMatrix AES.wordSuperboxKernel 0 y v ^ 2) ≤ kappa := by
    intro x
    exact (AllColumnBound.actual_word_residual_column_energy_lt x).le
  have he := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : Retained pOut => i = s) (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn (doubleMask u v)) mu (doubleRetainedFreeEquiv pOut pIn u v huv s)
    (doubleRetainedFreeEquiv_apply pOut pIn u v huv s) rho kappa kappa_nonneg hT hc
  have hfree := line_freeCoordinates_card pOut s
  have hdep := line_dependentCoordinates_card pOut s
  simp only [Finset.prod_const, Finset.card_univ] at he
  -- Normalize finite cardinalities across the local DecidablePred instances.
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  simpa only [hfree, hdep, pow_one] using he

theorem double_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (doubleMask u v) h y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  have he := double_code_response_energy pOut pIn u v huv
    (fun c => h (eventResidualTuple pOut pIn (doubleMask u v) c))
  rw [double_amplitude_energy pOut pIn u v huv h] at he
  exact he

theorem single_zeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  rw [single_zeroResponse_eq]
  exact single_response_energy pOut pIn u h

theorem double_intersectionResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (bareKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  rw [double_intersectionResponse_eq]
  exact double_response_energy pOut pIn u v huv h

/-- Exact kernel-zero premise at the three original input uniform labels. -/
theorem triple_zero_kernel (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    c.val u.val.val = 0 → c.val v.val.val = 0 → c.val w.val.val = 0 →
      bareKernel pOut pIn y c = 0 := by
  intro hu hv hw
  have hz := triple_zero_source pOut pIn u v w huv huw hvw c hu hv hw
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  unfold bareKernel
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  change residualMatrix AES.wordSuperboxKernel 0 (y s)
    (WordCrossZero.wordMixAddEquiv c.val s.val) = 0
  rw [hz, map_zero, Pi.zero_apply, AES.word_residual_zero_column]

end AESConcrete.OmittedUniformTwoOutputEventEnergy
