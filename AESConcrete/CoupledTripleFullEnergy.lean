import AESConcrete.CoupledTripleFiber
import AESConcrete.DoubleUniformFourierEnergy

/-!
# Raw full-response energy for an arbitrary joint residual triple

The source is every physical four-word input, including zero values. Its
retained-triple map is noninjective, so the arbitrary signed joint amplitude
is first summed over the actual fibers. The ORIGINAL scalar uniform input
translation gives two free Fourier coordinates and one dependent coordinate.
The inverse 3-by-3 MDS pullback is bijective: the exact fiber factor is q^2,
with no additional q multiplicity. No factorization, centering, positivity,
axis-zero condition, cancellation or nonzero-uniform normalization is assumed.
Only the ordinary/ordinary/false two-sided operator and column resources are
used. All three nonempty exclusion responses remain separate obligations.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleFullEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.IndexedGraphEnergy
open AESConcrete.CoupledTripleFiber
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

/-- Raw counting response over the entire physical source, including every
zero value. There are three retained residual kernels and no uniform weights. -/
def rawFullResponse (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : RetainedPositions pOut → AES.Word) : ℝ :=
  ∑ s : AES.WordState, h (residualHom pIn s) *
    ∏ i : RetainedPositions pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (wordMixAddEquiv s i.val)

/-- The existing response interface preserves the full four-word source;
it does not replace the noninjective retained map by an equivalence. -/
theorem rawFullResponse_eq_response
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (y : RetainedPositions pOut → AES.Word) :
    rawFullResponse pIn pOut h y =
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (retainedHom wordMixAddEquiv pOut)
        (fun s : AES.WordState => h (residualHom pIn s)) y := rfl

/-- `zeroExtend` is a finite pushforward sum even for a noninjective map.
Here that sum is exactly the actual retained fiber sum. -/
theorem wordFiberAmplitude_eq_pushforward
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ)
    (x : RetainedPositions pOut → AES.Word) :
    wordFiberAmplitude pIn pOut h x =
      InvariantSubspaceEnergy.zeroExtend (retainedHom wordMixAddEquiv pOut)
        (fun s : AES.WordState => h (residualHom pIn s)) x := by
  -- Reuse the repaired generic sum proof, before the enormous word Fintype.
  -- Pointwise summand and Fintype-enumeration alignment are both explicit.
  have hpush {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V]
      (L : (Fin 4 → V) ≃+ (Fin 4 → V))
      (pIn pOut : SelectedSupport 3 4)
      (h : (ResidualPositions pIn → V) → ℝ)
      (x : RetainedPositions pOut → V) :
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
    (pIn pOut : SelectedSupport 3 4)
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

/-- The ORIGINAL scalar uniform input direction determines the singleton
dependent Fourier tuple. The other two retained frequencies remain free. -/
theorem rawFullResponse_energy_le_fiber_at
    (pIn pOut : SelectedSupport 3 4)
    (s : RetainedPositions pOut) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : RetainedPositions pOut => i ≠ s)) = 2 :=
    ThreeActiveGeometry.retained_other_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : RetainedPositions pOut => i ≠ s)) = 1 :=
    IndexedFourierSupport.dependentCoordinates_card s
  have hsurj : Function.Surjective
      (fun t : AES.Word =>
        fun j : DependentCoordinates (fun i : RetainedPositions pOut => i ≠ s) =>
          wordUniformTranslation pIn pOut t j.val) :=
    InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
      (wordUniformTranslation pIn pOut)
      (word_originalUniform_retained_singleton_bijective pIn pOut s).surjective
  have he := InvariantSubspaceFourier.coordinate_fourier_partial_graph_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : RetainedPositions pOut => i ≠ s)
    (fun _ => UniformGraphScalar.rho) (fun _ => UniformGraphScalar.kappa)
    (fun _ => UniformGraphScalar.kappa_nonneg)
    (fun _ => DoubleUniformFourierEnergy.word_fourier_operator_energy)
    (fun _ => DoubleUniformFourierEnergy.word_fourier_column_energy)
    (wordUniformTranslation pIn pOut) hsurj
    (wordFiberAmplitude pIn pOut h)
    (word_fiberAmplitude_originalUniform_translation pIn pOut h)
  simp only [Finset.prod_const, Finset.card_univ] at he
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep] at he
  simp_rw [rawFullResponse_eq_coordinate_action]
  simpa only [pow_one, ← pow_mul] using he

/-- Remove the auxiliary dependent label using the nonempty actual retained
triple. The response and its bound contain no chosen coordinate. -/
theorem rawFullResponse_energy_le_fiber
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 := by
  classical
  haveI : Nonempty (RetainedPositions pOut) :=
    Fintype.card_pos_iff.mp (by
      rw [ThreeActiveGeometry.retainedCoordinates_card]
      norm_num)
  exact rawFullResponse_energy_le_fiber_at pIn pOut (Classical.choice inferInstance) h

/-- The exact q^2 fiber-energy identity preserves the coupled-line average.
The inverse 3-by-3 residual pullback is bijective and adds no q multiplicity. -/
theorem rawFullResponse_energy_le_average
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (ActivityCodeScalar.q ^ 2 * UniformGraphScalar.rho ^ 4 *
        UniformGraphScalar.kappa) *
          ∑ u, CoupledLineAverage.average (wordD pIn pOut) h u ^ 2 := by
  have he := rawFullResponse_energy_le_fiber pIn pOut h
  rw [word_fiberAmplitude_energy_exact, DoubleUniformFourierEnergy.word_card_real] at he
  exact he.trans_eq (by ring)

/-- Full raw counting-response energy for every arbitrary signed joint h.
The exact q^2 fiber factor and average contraction require no cancellation. -/
theorem rawFullResponse_energy
    (pIn pOut : SelectedSupport 3 4)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawFullResponse pIn pOut h y ^ 2) ≤
      (ActivityCodeScalar.q ^ 2 * UniformGraphScalar.rho ^ 4 *
        UniformGraphScalar.kappa) * ∑ u, h u ^ 2 := by
  calc
    _ ≤ (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ x, wordFiberAmplitude pIn pOut h x ^ 2 :=
      rawFullResponse_energy_le_fiber pIn pOut h
    _ ≤ (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ((Fintype.card AES.Word : ℝ) ^ 2 * ∑ u, h u ^ 2) :=
      mul_le_mul_of_nonneg_left (word_fiberAmplitude_energy_le pIn pOut h)
        (mul_nonneg (pow_nonneg UniformGraphScalar.rho_nonneg 4)
          UniformGraphScalar.kappa_nonneg)
    _ = _ := by
      rw [DoubleUniformFourierEnergy.word_card_real]
      ring

end AESConcrete.CoupledTripleFullEnergy
