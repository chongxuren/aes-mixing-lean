import AESConcrete.CoupledPairFiber
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Raw full-response energy for an arbitrary joint residual pair

The fiber identities are supplied by `CoupledPairFiber`.

The full source is every physical four-word input. Its retained-triple map is
not injective: the amplitude must first be summed over the actual fibers. The
signed residual-pair amplitude is arbitrary and joint. No factorization,
centering, axis-zero condition, full-response cancellation or nonzero-uniform
normalization is assumed. The only Fourier resources are the actual
ordinary/ordinary/false two-sided operator and column estimates.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.IndexedGraphEnergy
open AESConcrete.CoupledPairFiber
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

/-- Raw counting response over the entire physical source, including every
zero value. There are three retained residual kernels and no uniform weights. -/
def rawFullResponse (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : RetainedPositions pOut → AES.Word) : ℝ :=
  ∑ s : AES.WordState, h (residualHom pIn s) *
    ∏ i : RetainedPositions pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv s i.val)

/-- The existing response interface preserves the full four-word source;
it does not replace the noninjective retained map by an equivalence. -/
theorem rawFullResponse_eq_response
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : RetainedPositions pOut → AES.Word) :
    rawFullResponse pIn pOut h y =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (retainedHom wordMixAddEquiv pOut)
        (fun s : AES.WordState => h (residualHom pIn s)) y := rfl

/-- `zeroExtend` is defined as a finite pushforward sum even for a
noninjective map. Here that sum is exactly the actual retained fiber sum. -/
theorem wordFiberAmplitude_eq_pushforward
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (x : RetainedPositions pOut → AES.Word) :
    wordFiberAmplitude pIn pOut h x =
      InvariantSubspaceEnergy.zeroExtend (retainedHom wordMixAddEquiv pOut)
        (fun s : AES.WordState => h (residualHom pIn s)) x := by
  -- Prove the finite-sum identity before specializing the enormous word Fintype.
  have hpush {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V]
      (L : (Fin 4 → V) ≃+ (Fin 4 → V))
      (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
      (h : (ResidualPositions pIn → V) → ℝ) (x : RetainedPositions pOut → V) :
      fiberAmplitude L pIn pOut h x =
        InvariantSubspaceEnergy.zeroExtend (retainedHom L pOut)
          (fun s : Fin 4 → V => h (residualHom pIn s)) x := by
    classical
    unfold fiberAmplitude InvariantSubspaceEnergy.zeroExtend
    symm
    calc
      _ = ∑ s : Fin 4 → V,
          if retainedHom L pOut s = x then h (residualHom pIn s) else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : retainedHom L pOut s = x <;> simp [hs]
      _ = ∑ s : RetainedFiber L pOut x, h (residualHom pIn s.val) := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) _
      _ = _ := Finset.sum_congr
        (congrArg (@Fintype.elems (RetainedFiber L pOut x))
          (Subsingleton.elim _ _)) (fun _ _ => rfl)
  unfold wordFiberAmplitude
  exact hpush wordMixAddEquiv pIn pOut h x

/-- Exact regrouping by the actual retained triple. This finite-sum identity
requires no injectivity and introduces no cardinality or normalization factor. -/
theorem rawFullResponse_eq_coordinate_action
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : RetainedPositions pOut → AES.Word) :
    rawFullResponse pIn pOut h y =
      action (coordinateKernel (fun _ : RetainedPositions pOut =>
        residualMatrix AES.wordSuperboxKernel 0)) (wordFiberAmplitude pIn pOut h) y := by
  have hf : InvariantSubspaceEnergy.zeroExtend (retainedHom wordMixAddEquiv pOut)
      (fun s : AES.WordState => h (residualHom pIn s)) =
      wordFiberAmplitude pIn pOut h := by
    funext x
    exact (wordFiberAmplitude_eq_pushforward pIn pOut h x).symm
  rw [rawFullResponse_eq_response, InvariantSubspaceEnergy.response_eq_action, hf]

/-- The two ORIGINAL uniform input directions determine both dependent
Fourier coordinates jointly. One retained frequency remains free. -/
theorem rawFullResponse_energy_le_fiber_at
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : RetainedPositions pOut => i = s)) = 1 :=
    Fintype.card_subtype_eq s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : RetainedPositions pOut => i = s)) = 2 :=
    DoubleUniformGeometry.retained_other_card pOut s
  have hsurj : Function.Surjective
      (fun t : OriginalUniformPositions pIn → AES.Word =>
        fun j : DependentCoordinates (fun i : RetainedPositions pOut => i = s) =>
          originalUniformTranslation wordMixAddEquiv pIn pOut t j.val) :=
    (word_originalUniform_retained_pair_bijective pIn pOut s).surjective
  have he := InvariantSubspaceFourier.coordinate_fourier_partial_graph_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : RetainedPositions pOut => i = s)
    (fun _ => UniformGraphScalar.rho) (fun _ => UniformGraphScalar.kappa)
    (fun _ => UniformGraphScalar.kappa_nonneg)
    (fun _ => DoubleUniformFourierEnergy.word_fourier_operator_energy)
    (fun _ => DoubleUniformFourierEnergy.word_fourier_column_energy)
    (originalUniformTranslation wordMixAddEquiv pIn pOut) hsurj
    (wordFiberAmplitude pIn pOut h)
    (word_fiberAmplitude_originalUniform_translation pIn pOut h)
  simp only [Finset.prod_const, Finset.card_univ] at he
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep] at he
  simp_rw [rawFullResponse_eq_coordinate_action]
  simpa only [pow_one] using he

/-- The auxiliary free retained label is removed using the nonempty actual
retained triple. The response and its bound contain no chosen coordinate. -/
theorem rawFullResponse_energy_le_fiber
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 := by
  classical
  haveI : Nonempty (RetainedPositions pOut) :=
    Fintype.card_pos_iff.mp (by
      rw [ThreeActiveGeometry.retainedCoordinates_card]
      norm_num)
  exact rawFullResponse_energy_le_fiber_at pIn pOut (Classical.choice inferInstance) h

/-- The exact q^3 fiber-energy identity preserves the coupled-line average.
No claim that this average vanishes is used. -/
theorem rawFullResponse_energy_le_average
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (ActivityCodeScalar.q ^ 3 * UniformGraphScalar.rho ^ 2 *
        UniformGraphScalar.kappa ^ 2) *
          ∑ u, CoupledLineAverage.average (wordD pIn pOut) h u ^ 2 := by
  have he := rawFullResponse_energy_le_fiber pIn pOut h
  rw [word_fiberAmplitude_energy_exact, DoubleUniformFourierEnergy.word_card_real] at he
  exact he.trans_eq (by ring)

/-- Full raw counting-response energy for every arbitrary signed joint h.
The q^3 factor comes from the actual fiber amplitude, not an injective-source
energy identity or a product-amplitude assumption. -/
theorem rawFullResponse_energy
    (pIn : SelectedSupport 2 4) (pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (ActivityCodeScalar.q ^ 3 * UniformGraphScalar.rho ^ 2 *
        UniformGraphScalar.kappa ^ 2) * ∑ u, h u ^ 2 := by
  calc
    _ ≤ (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 :=
      rawFullResponse_energy_le_fiber pIn pOut h
    _ ≤ (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2) *
        ((Fintype.card AES.Word : ℝ) ^ 3 * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left (word_fiberAmplitude_energy_le pIn pOut h)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by
      rw [DoubleUniformFourierEnergy.word_card_real]
      ring

end AESConcrete.CoupledPairFullEnergy
