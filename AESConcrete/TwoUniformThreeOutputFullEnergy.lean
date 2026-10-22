import AESConcrete.TwoUniformThreeOutputGeometry
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Raw full-source energy for three outputs and a joint residual pair

Lemmas for (11,10). The actual output-zero code has exactly q copies of each
original residual pair. Its residual-zero translation line projects onto any
retained output label. The generic Fourier theorem therefore charges two free
ordinary operator factors and one ordinary column factor, giving
q*rho^4*kappa.

The amplitude h is arbitrary and signed, with no factorization, residuality,
positivity, independence, cancellation or desired-bound premise. Geometry and
exact source energy are imported from the geometry module.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

This module asserts no normalized response, event bound, physical cap,
certificate or full AES theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoUniformThreeOutputFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoUniformThreeOutputGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy
  (word_card_real word_fourier_operator_energy word_fourier_column_energy)

set_option maxRecDepth 100000

/-- Actual raw response, before either original nonzero-uniform normalization. -/
def rawFullResponse (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => h (residualTuple pOut pIn c)) y

theorem rawFullResponse_energy_at
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (s : Retained pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 2 :=
    freeCoordinates_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
    dependentCoordinates_card pOut s
  have henergy : (∑ c : Code pOut pIn, h (residualTuple pOut pIn c) ^ 2) =
      q * ∑ u, h u ^ 2 := by
    rw [full_amplitude_energy pOut pIn h, word_card_real]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : Retained pOut => i ≠ s) rho kappa kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy
    (retainedHom pOut pIn) (retainedHom_injective pOut pIn)
    (translation pOut pIn) (translation_dependent_surjective pOut pIn s)
    (fun c => h (residualTuple pOut pIn c)) (amplitude_translation pOut pIn h)
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, henergy] at he
  exact he.trans_eq (by ring)

/-- The same arbitrary signed joint amplitude, with no auxiliary hypotheses. -/
theorem rawFullResponse_energy
    (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact rawFullResponse_energy_at pOut pIn (Classical.choice inferInstance) h

end AESConcrete.TwoUniformThreeOutputFullEnergy
