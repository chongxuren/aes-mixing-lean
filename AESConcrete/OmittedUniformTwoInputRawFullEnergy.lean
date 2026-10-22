import AESConcrete.OmittedUniformTwoInputRawGeometry
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Raw (9,10) response through noninjective retained pushforward

The source is the exact one-output-zero code for selected output (2,3),
selected input (2,4). h is arbitrary, signed and JOINT on the original pair,
including h(0,0). Its raw code energy is q times the original joint energy;
the retained pushforward costs a further factor q from its exact fibers.

The retained pushforward is invariant under the actual residual-zero line. Its
ordinary Fourier support has one free and one dependent coordinate. The
ambient graph theorem gives rho^2*kappa, so the complete proposed raw
coefficient is q^2*rho^2*kappa. The injective response wrapper is UNUSED.

No normalized source, input-zero exclusion, omitted-output split, selected
minor, physical cap, certificate or full AES theorem is
proved. Fixed constructive AES10/14/16; independent uniform retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.OmittedUniformTwoInputRawFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.InvariantSubspaceEnergy (zeroExtend)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates splitCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy
  (word_card_real word_fourier_operator_energy word_fourier_column_energy)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- Exact physical retained-fiber size, in the same real q used downstream. -/
theorem retained_fiber_card_q (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (z : Retained pOut → AES.Word) :
    (Fintype.card {c : Code pOut pIn // retainedHom pOut pIn c = z} : ℝ) = q := by
  rw [retained_fiber_card pOut pIn j z, word_card_real]

/-- This is a finite FIBER SUM; the retained map is not injective. -/
def pushedAmplitude (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  zeroExtend (retainedHom pOut pIn) (fun c => h (residualTuple pOut pIn c))

theorem pushedAmplitude_eq_section (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (h : (Residual pIn → AES.Word) → ℝ)
    (z : Retained pOut → AES.Word) :
    pushedAmplitude pOut pIn h z = ∑ u : AES.Word,
      h (residualTuple pOut pIn ((retainedFiberParam pOut pIn j).symm (u, z))) :=
  OmittedUniformTwoInputPushforward.pushforward_eq_sum (retainedHom pOut pIn)
    (retainedFiberParam pOut pIn j) (retainedFiberParam_snd pOut pIn j)
    (fun c => h (residualTuple pOut pIn c)) z

/-- Exact fiber size q and exact source multiplicity q give an energy
INEQUALITY q^2 times the original JOINT h energy. -/
theorem pushedAmplitude_energy_at (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (j : Residual pIn) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ z, pushedAmplitude pOut pIn h z ^ 2) ≤ q ^ 2 * ∑ u, h u ^ 2 := by
  have he := OmittedUniformTwoInputPushforward.pushforward_energy_le
    (retainedHom pOut pIn) (retainedFiberParam pOut pIn j)
    (retainedFiberParam_snd pOut pIn j) (fun c => h (residualTuple pOut pIn c))
  rw [full_amplitude_energy pOut pIn h, word_card_real] at he
  exact he.trans_eq (by ring)

theorem pushedAmplitude_energy (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ z, pushedAmplitude pOut pIn h z ^ 2) ≤ q ^ 2 * ∑ u, h u ^ 2 := by
  haveI : Nonempty (Residual pIn) :=
    Fintype.card_pos_iff.mp (by rw [residualCoordinates_card]; norm_num)
  exact pushedAmplitude_energy_at pOut pIn (Classical.choice inferInstance) h

/-- The existing finite-pushforward translation identity needs no injectivity.
Both original residual coordinates are preserved before applying h. -/
theorem pushedAmplitude_translation (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (z : Retained pOut → AES.Word)
    (t : ResidualZero pOut pIn) :
    pushedAmplitude pOut pIn h
      (z + retainedHom pOut pIn (translation pOut pIn t)) =
      pushedAmplitude pOut pIn h z :=
  InvariantSubspaceEnergy.zeroExtend_translation (retainedHom pOut pIn)
    (translation pOut pIn) (fun c => h (residualTuple pOut pIn c))
    (amplitude_translation pOut pIn h) z t

/-- Complete actual graph premise for the AMBIENT Fourier energy theorem.
The dependent label is forced by the actual residual-zero translation line. -/
theorem pushed_fourier_fiber_unique
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4) (s : Retained pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    ∀ (w : FreeCoordinates (fun i : Retained pOut => i ≠ s) → AES.Word)
      (v v' : DependentCoordinates (fun i : Retained pOut => i ≠ s) → AES.Word),
      action (coordinateKernel (fun _ : Retained pOut =>
        pairingFourier WordFourierCore.wordPairing)) (pushedAmplitude pOut pIn h)
        ((splitCoordinates (fun i : Retained pOut => i ≠ s)).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : Retained pOut =>
        pairingFourier WordFourierCore.wordPairing)) (pushedAmplitude pOut pIn h)
        ((splitCoordinates (fun i : Retained pOut => i ≠ s)).symm (v', w)) ≠ 0 → v = v' :=
  InvariantSubspaceFourier.invariant_fourier_fiber_unique
    WordFourierCore.wordPairing word_add_self (fun i : Retained pOut => i ≠ s)
    (fun t : ResidualZero pOut pIn => retainedHom pOut pIn (translation pOut pIn t))
    (translation_dependent_surjective pOut pIn s)
    (pushedAmplitude pOut pIn h) (pushedAmplitude_translation pOut pIn h)

/-- Actual raw response, before either original input-uniform normalization
and before the omitted-output uniform subtraction. -/
def rawFullResponse (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => h (residualTuple pOut pIn c)) y

theorem rawFullResponse_eq_action (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    rawFullResponse pOut pIn h y = action
      (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0))
      (pushedAmplitude pOut pIn h) y :=
  InvariantSubspaceEnergy.response_eq_action (residualMatrix AES.wordSuperboxKernel 0)
    (retainedHom pOut pIn) (fun c => h (residualTuple pOut pIn c)) y

/-- One free Fourier operator and one dependent Fourier column are applied
to the noninjective retained pushforward, with its full q^2 energy factor. -/
theorem rawFullResponse_energy_at
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (s : Retained pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  have hfree : Fintype.card
      (FreeCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
    freeCoordinates_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : Retained pOut => i ≠ s)) = 1 :=
    dependentCoordinates_card pOut s
  have he := IndexedGraphEnergy.coordinate_fourier_partial_graph_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : Retained pOut => i ≠ s) (fun _ => rho) (fun _ => kappa)
    (fun _ => kappa_nonneg) (fun _ => word_fourier_operator_energy)
    (fun _ => word_fourier_column_energy)
    (pushedAmplitude pOut pIn h) (pushed_fourier_fiber_unique pOut pIn s h)
  simp only [Finset.prod_const, Finset.card_univ] at he
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep] at he
  have he' : (∑ y, action
      (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0))
      (pushedAmplitude pOut pIn h) y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ z, pushedAmplitude pOut pIn h z ^ 2 := by
    simpa only [pow_one] using he
  calc
    (∑ y, rawFullResponse pOut pIn h y ^ 2) = ∑ y, action
        (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0))
        (pushedAmplitude pOut pIn h) y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [rawFullResponse_eq_action]
    _ ≤ (rho ^ 2 * kappa) * ∑ z, pushedAmplitude pOut pIn h z ^ 2 := he'
    _ ≤ (rho ^ 2 * kappa) * (q ^ 2 * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left (pushedAmplitude_energy pOut pIn h)
        (mul_nonneg (sq_nonneg rho) kappa_nonneg)
    _ = (q ^ 2 * rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by ring

/-- Endpoint: arbitrary original joint h, including its value at the zero pair.
There are no desired-bound, centering, positivity or factorization hypotheses. -/
theorem rawFullResponse_energy
    (pOut : SelectedSupport 2 3) (pIn : SelectedSupport 2 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pOut pIn h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa) * ∑ u, h u ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact rawFullResponse_energy_at pOut pIn (Classical.choice inferInstance) h

end AESConcrete.OmittedUniformTwoInputRawFullEnergy
