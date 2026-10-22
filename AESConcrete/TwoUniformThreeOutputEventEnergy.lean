import AESConcrete.TwoUniformThreeOutputEventGeometry
import AESConcrete.ThreeActivePlaneEnergy

/-!
# Response energies for the two original input-zero exclusions

Lemmas for (11,10). The companion EventGeometry module owns physical masks,
information sets and exact source transports. Here its singleton planes use
two operator factors and one column factor; its double-zero line uses one
operator and two column factors. The same arbitrary signed JOINT residual-pair
h is preserved.

No factorization, positivity, centering, cancellation or desired-bound premise
is assumed. Constructive fixed AES10/14/16, independent uniform retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.

No FullEnergy module is imported.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoUniformThreeOutputEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry
  (Code Retained Residual SourceUniformPositions residualTuple retainedCoordinates_card)
open AESConcrete.TwoUniformThreeOutputEventGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem single_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (singleMask u) h y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ x, h x ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  exact ThreeActivePlaneEnergy.word_plane_residual_energy
    (retainedCoordinates_card pOut) s (eventCurve pOut pIn (singleMask u))
    (Equiv.ofBijective _ (single_residual_bijective pOut pIn u)) h
    (single_retained_pair_bijective pOut pIn u s)

/-- One output zero and two distinct actual input zeros leave a line. -/
theorem double_code_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (mu : EventCode pOut pIn (doubleMask u v) → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (eventCurve pOut pIn (doubleMask u v)) mu y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ c, mu c ^ 2 := by
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
  simpa only [Finset.prod_const, Finset.card_univ, FreeCoordinates,
    Fintype.card_subtype_eq, WeightedThreeOutputGeometry.line_dependentCoordinates_card pOut s,
    pow_one] using he

-- Editorial boundary: injection gives subenergy; do not strengthen it to equality.
theorem double_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (doubleMask u v) h y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ x, h x ^ 2 :=
  (double_code_response_energy pOut pIn u v huv
    (fun c => h (eventResidualTuple pOut pIn (doubleMask u v) c))).trans
      (mul_le_mul_of_nonneg_left (double_amplitude_energy_le pOut pIn u v huv h)
        (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)))

/--
These endpoints match the original-source response interface.
-/
theorem single_zeroResponse_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ x, h x ^ 2 := by
  rw [single_zeroResponse_eq]
  exact single_response_energy pOut pIn u h

theorem double_intersectionResponse_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ x, h x ^ 2 := by
  rw [double_intersectionResponse_eq]
  exact double_response_energy pOut pIn u v huv h

end AESConcrete.TwoUniformThreeOutputEventEnergy
