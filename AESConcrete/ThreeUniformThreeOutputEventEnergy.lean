import AESConcrete.ThreeUniformThreeOutputEventGeometry
import AESConcrete.ThreeActivePlaneEnergy
import AESConcrete.ActivityCodeScalar

/-!
# Plane, line and triple-zero kernel guarantees for three input uniforms

Lemmas for (11,7). Single-zero planes have energy q*rho^4*kappa and distinct
double-zero lines have energy rho^2*kappa^2, each against the same original
residual-tuple sum of h squared. In particular h(0) is retained. The triple-
zero kernel vanishes because MDS forces the physical source to zero and the
actual residual kernel has a zero column, not because the amplitude vanishes.

Geometry, exact source counting and response bounds have separate roles. No
full-code Geometry or FullEnergy is imported. Constructive fixed AES10/14/16;
independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeUniformThreeOutputEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry
  (Code Retained Residual SourceUniformPositions residualTuple retainedCoordinates_card)
open AESConcrete.ThreeUniformThreeOutputEventGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem single_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (singleMask u) h y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ x, h x ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have he := ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (retainedCoordinates_card pOut) s (eventCurve pOut pIn (singleMask u))
    (fun c => h (eventResidualTuple pOut pIn (singleMask u) c))
    (single_retained_pair_bijective pOut pIn u s)
  have hcard : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  calc
    _ ≤ (rho ^ 4 * kappa) * ∑ c : EventCode pOut pIn (singleMask u),
        h (eventResidualTuple pOut pIn (singleMask u) c) ^ 2 := he
    _ = (q * rho ^ 4 * kappa) * ∑ x, h x ^ 2 := by
      rw [single_amplitude_energy pOut pIn u h, hcard]
      ring

/-- One output zero and two distinct actual input zeros leave a line. -/
theorem double_code_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
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

/-- Exact residual parametrization retains the complete original energy. -/
theorem double_response_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (doubleMask u v) h y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ x, h x ^ 2 := by
  have he := double_code_response_energy pOut pIn u v huv
    (fun c => h (eventResidualTuple pOut pIn (doubleMask u v) c))
  rw [double_amplitude_energy pOut pIn u v huv h] at he
  exact he

/--
These endpoints match the original-source response interface.
-/
theorem single_zeroResponse_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, WeightedResponse.zeroResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ x, h x ^ 2 := by
  rw [single_zeroResponse_eq]
  exact single_response_energy pOut pIn u h

theorem double_intersectionResponse_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, TripleResponse.intersectionResponse
      (fun c : Code pOut pIn => h (residualTuple pOut pIn c))
      (baseKernel pOut pIn) (fun c => c.val u.val.val) (fun c => c.val v.val.val) y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ x, h x ^ 2 := by
  rw [double_intersectionResponse_eq]
  exact double_response_energy pOut pIn u v huv h

/-- The exact SevenResponse hzero premise; h(0) is unrestricted. -/
theorem triple_zero_kernel (pOut : SelectedSupport 3 3) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) :
    c.val u.val.val = 0 → c.val v.val.val = 0 → c.val w.val.val = 0 →
      baseKernel pOut pIn y c = 0 := by
  intro hu hv hw
  have hz := triple_zero_source pOut pIn u v w huv huw hvw c hu hv hw
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  unfold baseKernel
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [hz, map_zero, Pi.zero_apply, AES.word_residual_zero_column]

end AESConcrete.ThreeUniformThreeOutputEventEnergy
