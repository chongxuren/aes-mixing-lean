import AESConcrete.TwoOmittedOneInputSource
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Full q^3 finite-pushforward and ambient Fourier bound for (10,12)

Full source energy qH, actual q^2 fibers and finite Cauchy give q^3H for the
signed pushforward. Ambient invariance and whole singleton-dependent Fourier
support then give rho^2*kappa. The generic finite-pushforward helper supplies
its own proof. Constructive fixed AES10/14/16.

No injectivity wrapper or (9,10) endpoint is used.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputSource
open AESConcrete.InvariantSubspaceEnergy (zeroExtend)
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates splitCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.DoubleUniformFourierEnergy
  (word_card_real word_fourier_operator_energy word_fourier_column_energy)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem full_fiber_factor (pIn : SelectedSupport 3 4) :
    (Fintype.card (MaskCoordinates (residualPairMask pIn) → AES.Word) : ℝ) = q ^ 2 := by
  rw [Fintype.card_fun, maskCoordinates_card, residualPairMask_size,
    Nat.cast_pow, word_card_real]

theorem full_retained_fiber_card (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (z : Retained pOut → AES.Word) :
    (Fintype.card {x : AES.WordState // retainedHom pOut x = z} : ℝ) = q ^ 2 := by
  -- Nat.card removes the provider's subtype counting-instance choice before casting.
  have hc : Fintype.card {x : AES.WordState // retainedHom pOut x = z} =
      Fintype.card (MaskCoordinates (residualPairMask pIn) → AES.Word) := by
    simpa only [← Nat.card_eq_fintype_card] using
      (OmittedUniformTwoInputPushforward.fiber_card (retainedHom pOut)
        (fullRetainedFiberParam pOut pIn) (fullRetainedFiberParam_snd pOut pIn) z)
  exact (congrArg (fun n : ℕ => (n : ℝ)) hc).trans (full_fiber_factor pIn)

def pushedAmplitude (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) : (Retained pOut → AES.Word) → ℝ :=
  zeroExtend (retainedHom pOut) (psi pIn h)

theorem pushedAmplitude_eq_section (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (z : Retained pOut → AES.Word) :
    pushedAmplitude pOut pIn h z =
      ∑ u : MaskCoordinates (residualPairMask pIn) → AES.Word,
        psi pIn h ((fullRetainedFiberParam pOut pIn).symm (u,z)) :=
  OmittedUniformTwoInputPushforward.pushforward_eq_sum (retainedHom pOut)
    (fullRetainedFiberParam pOut pIn) (fullRetainedFiberParam_snd pOut pIn) (psi pIn h) z

/-- q^2 actual-fiber Cauchy times q exact source multiplicity; not zero-extension equality. -/
theorem pushedAmplitude_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ z, pushedAmplitude pOut pIn h z ^ 2) ≤ q ^ 3 * ∑ r, h r ^ 2 := by
  have he := OmittedUniformTwoInputPushforward.pushforward_energy_le
    (retainedHom pOut) (fullRetainedFiberParam pOut pIn)
    (fullRetainedFiberParam_snd pOut pIn) (psi pIn h)
  rw [full_fiber_factor pIn, full_psi_energy pIn h] at he
  exact he.trans_eq (by ring)

theorem pushedAmplitude_translation (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (z : Retained pOut → AES.Word)
    (t : ResidualZero pIn) :
    pushedAmplitude pOut pIn h (z + retainedHom pOut (translation pIn t)) =
      pushedAmplitude pOut pIn h z :=
  InvariantSubspaceEnergy.zeroExtend_translation (retainedHom pOut) (translation pIn)
    (psi pIn h) (amplitude_translation pIn h) z t

/-- The complete dependent tuple, not separate coordinates, is determined. -/
theorem pushed_fourier_fiber_unique (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (s : Retained pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    ∀ (w : FreeCoordinates (fun i : Retained pOut => i ≠ s) → AES.Word)
      (v v' : DependentCoordinates (fun i : Retained pOut => i ≠ s) → AES.Word),
      action (coordinateKernel (fun _ : Retained pOut => pairingFourier WordFourierCore.wordPairing))
        (pushedAmplitude pOut pIn h)
        ((splitCoordinates (fun i : Retained pOut => i ≠ s)).symm (v,w)) ≠ 0 →
      action (coordinateKernel (fun _ : Retained pOut => pairingFourier WordFourierCore.wordPairing))
        (pushedAmplitude pOut pIn h)
        ((splitCoordinates (fun i : Retained pOut => i ≠ s)).symm (v',w)) ≠ 0 → v = v' :=
  InvariantSubspaceFourier.invariant_fourier_fiber_unique
    WordFourierCore.wordPairing word_add_self (fun i : Retained pOut => i ≠ s)
    (fun t : ResidualZero pIn => retainedHom pOut (translation pIn t))
    (translation_dependent_surjective pOut pIn s)
    (pushedAmplitude pOut pIn h) (pushedAmplitude_translation pOut pIn h)

theorem rawResponse_eq_action (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    rawResponse pOut pIn h y = action
      (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0))
      (pushedAmplitude pOut pIn h) y :=
  InvariantSubspaceEnergy.response_eq_action (residualMatrix AES.wordSuperboxKernel 0)
    (retainedHom pOut) (psi pIn h) y

/-- Actual two-sided Fourier operator/column resources applied to the ambient F. -/
theorem rawResponse_energy_at (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (s : Retained pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤
      (q ^ 3 * rho ^ 2 * kappa) * ∑ r, h r ^ 2 := by
  have hfree := freeCoordinates_card pOut s
  have hdep := dependentCoordinates_card pOut s
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
    _ = ∑ y, action
        (coordinateKernel (fun _ : Retained pOut => residualMatrix AES.wordSuperboxKernel 0))
        (pushedAmplitude pOut pIn h) y ^ 2 := by simp_rw [rawResponse_eq_action]
    _ ≤ (rho ^ 2 * kappa) * ∑ z, pushedAmplitude pOut pIn h z ^ 2 := he'
    _ ≤ (rho ^ 2 * kappa) * (q ^ 3 * ∑ r, h r ^ 2) :=
      mul_le_mul_of_nonneg_left (pushedAmplitude_energy pOut pIn h)
        (mul_nonneg (sq_nonneg rho) kappa_nonneg)
    _ = _ := by ring

theorem rawResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, rawResponse pOut pIn h y ^ 2) ≤
      (q ^ 3 * rho ^ 2 * kappa) * ∑ r, h r ^ 2 := by
  haveI : Nonempty (Retained pOut) := Fintype.card_pos_iff.mp (by rw [retained_card]; norm_num)
  exact rawResponse_energy_at pOut pIn (Classical.choice inferInstance) h

end AESConcrete.TwoOmittedOneInputFullEnergy
