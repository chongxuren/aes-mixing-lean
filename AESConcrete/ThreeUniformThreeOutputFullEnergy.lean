import AESConcrete.ThreeUniformThreeOutputGeometry
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Full-source energy from an actual residual-zero translation plane

Lemmas for (11,7). The actual output-zero code has q^2 states per original
residual singleton. Its residual-zero translation plane projects jointly onto
the dependent pair of retained outputs. The generic Fourier theorem charges
one free ordinary operator factor and two ordinary column factors, giving
q^2*rho^2*kappa^2.

The original tuple amplitude h is arbitrary and signed, including h(0), with
no factorization, residuality, positivity, independence or desired-bound
premise. This module supplies only the raw full-response energy. Source
normalization, events, physical aggregation and certificate comparison belong
elsewhere.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeUniformThreeOutputFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ThreeUniformThreeOutputGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy
  (word_card_real word_fourier_operator_energy word_fourier_column_energy)

set_option maxRecDepth 100000

/-- Actual raw response before all three original nonzero-uniform weights. -/
def rawFullResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => h (residualTuple pOut pIn c)) y

theorem rawFullResponse_energy_at
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (s : Retained pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : Retained pOut => i = s)) = 1 :=
    freeCoordinates_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : Retained pOut => i = s)) = 2 :=
    dependentCoordinates_card pOut s
  have henergy : (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      q ^ 2 * ∑ u, h u ^ 2 := by
    rw [full_amplitude_energy pOut pIn h, word_card_real]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : Retained pOut => i = s) rho kappa kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy
    (retainedHom pOut pIn) (retainedHom_injective pOut pIn)
    (translation pOut pIn) (translation_dependent_surjective pOut pIn s)
    (fun c => h (residualTuple pOut pIn c)) (amplitude_translation pOut pIn h)
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, henergy] at he
  exact he.trans_eq (by ring)

/-- The original arbitrary signed amplitude is the sole source-energy comparator. -/
theorem rawFullResponse_energy
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact rawFullResponse_energy_at pOut pIn (Classical.choice inferInstance) h

end AESConcrete.ThreeUniformThreeOutputFullEnergy
