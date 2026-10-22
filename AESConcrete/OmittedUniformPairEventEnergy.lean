import AESConcrete.OmittedUniformPairEventGeometry
import AESConcrete.FiniteTensorEnergy
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar

/-!
# Actual pair-source singleton and double input-zero energies for (9,10)

RawGeometry and PairSource supply the source interfaces. The singleton input-
zero plane has both retained outputs as coordinates, so ordinary two-
coordinate tensorization gives rho^4 times the SAME arbitrary signed joint
residual-pair energy. The double-zero line has one free retained output and
one dependent column. Its joint residual image is only injective, giving
subenergy and rho^2*kappa.

No factorization, centering, zero-pair-value or desired-bound premise is used.
Both original uniform input labels are quantified in their original type.
Constructive fixed AES10/14/16, independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct reference.

No scalar comparison, selected-minor estimate or physical aggregation is
supplied here.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.OmittedUniformPairEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.OmittedUniformTwoInputRawGeometry
open AESConcrete.OmittedUniformPairEventGeometry
open AESConcrete.IndexedGraphEnergy (FreeCoordinates DependentCoordinates)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- Exact source reindexing followed by ordinary two-coordinate tensorization.
This helper imposes no factorization or sign restriction on the joint amplitude. -/
theorem response_energy_of_bijective (pOut : SelectedSupport 2 3)
    {C : Type*} [Fintype C] (curve : C → Retained pOut → AES.Word)
    (hc : Function.Bijective curve) (mu : C → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      curve mu y ^ 2) ≤ rho ^ 4 * ∑ c, mu c ^ 2 := by
  classical
  let e : C ≃ (Retained pOut → AES.Word) := Equiv.ofBijective curve hc
  let f : (Retained pOut → AES.Word) → ℝ := fun z => mu (e.symm z)
  have henergy : (∑ z, f z ^ 2) = ∑ c, mu c ^ 2 :=
    e.symm.sum_comp (fun c => mu c ^ 2)
  have hresponse (y : Retained pOut → AES.Word) :
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        curve mu y =
      action (coordinateKernel (fun _ : Retained pOut =>
        residualMatrix AES.wordSuperboxKernel 0)) f y := by
    unfold IndexedTripleEnergy.response action coordinateKernel
    rw [← e.symm.sum_comp (fun c => mu c * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (curve c i))]
    apply Finset.sum_congr rfl
    intro z _
    have hz : curve (e.symm z) = z := e.apply_symm_apply z
    rw [hz]
    exact mul_comm _ _
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤
        rho ^ 2 * ∑ x, g x ^ 2 := by
    intro g
    simpa only [rho] using SharpDampedWordNorm.word_superbox_residual_energy g
  have he := FiniteTensorEnergy.uniform_coordinate_energy
    (residualMatrix AES.wordSuperboxKernel 0) rho hT f
  simp_rw [← hresponse] at he
  rw [henergy] at he
  have hcard := retainedCoordinates_card pOut
  -- Cardinality is independent of local classical subtype decision instances.
  simp only [← Nat.card_eq_fintype_card] at he hcard
  rw [hcard] at he
  exact he

/-- A singleton input-zero event has two free retained output coordinates. -/
theorem single_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (singleMask u) h y ^ 2) ≤
      rho ^ 4 * ∑ x, h x ^ 2 := by
  have he := response_energy_of_bijective pOut
    (eventCurve pOut pIn (singleMask u)) (single_retained_bijective pOut pIn u)
    (fun c => h (eventResidualTuple pOut pIn (singleMask u) c))
  rw [single_amplitude_energy pOut pIn u h] at he
  exact he

/-- Actual double-zero line: one operator factor and one column factor. -/
theorem double_code_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (mu : EventCode pOut pIn (doubleMask u v) → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (eventCurve pOut pIn (doubleMask u v)) mu y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ c, mu c ^ 2 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let s : Retained pOut := Classical.choice inferInstance
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤
        rho ^ 2 * ∑ x, g x ^ 2 := by
    intro g
    simpa only [rho] using SharpDampedWordNorm.word_superbox_residual_energy g
  have hc : ∀ x : AES.Word,
      (∑ y, residualMatrix AES.wordSuperboxKernel 0 y x ^ 2) ≤ kappa := by
    intro x
    simpa only [kappa] using (AllColumnBound.actual_word_residual_column_energy_lt x).le
  have he := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : Retained pOut => i = s) (residualMatrix AES.wordSuperboxKernel 0)
    (eventCurve pOut pIn (doubleMask u v)) mu (doubleRetainedFreeEquiv pOut pIn u v huv s)
    (doubleRetainedFreeEquiv_apply pOut pIn u v huv s) rho kappa kappa_nonneg hT hc
  have hfree := line_freeCoordinates_card pOut s
  have hdep := line_dependentCoordinates_card pOut s
  simp only [Finset.prod_const, Finset.card_univ] at he
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  simpa only [hfree, hdep, pow_one] using he

theorem double_response_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, eventResponse pOut pIn (doubleMask u v) h y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  have he := double_code_response_energy pOut pIn u v huv
    (fun c => h (eventResidualTuple pOut pIn (doubleMask u v) c))
  exact he.trans (mul_le_mul_of_nonneg_left
    (double_amplitude_energy_le pOut pIn u v huv h)
    (mul_nonneg (sq_nonneg rho) kappa_nonneg))

/-- Public endpoint for either original input-uniform label, using the same h. -/
theorem single_zeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSource.zeroResponse pOut pIn u h y ^ 2) ≤
      rho ^ 4 * ∑ x, h x ^ 2 := by
  rw [single_zeroResponse_eq]
  exact single_response_energy pOut pIn u h

theorem first_zeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSource.zeroResponse pOut pIn
      (OmittedUniformTwoInputPairSource.uniformFirst pIn) h y ^ 2) ≤
      rho ^ 4 * ∑ x, h x ^ 2 :=
  single_zeroResponse_energy pOut pIn _ h

theorem second_zeroResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSource.zeroResponse pOut pIn
      (OmittedUniformTwoInputPairSource.uniformSecond pIn) h y ^ 2) ≤
      rho ^ 4 * ∑ x, h x ^ 2 :=
  single_zeroResponse_energy pOut pIn _ h

/-- The signed intersection is retained and bounded by residual subenergy. -/
theorem double_intersectionResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSource.intersectionResponse pOut pIn u v h y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ x, h x ^ 2 := by
  rw [double_intersectionResponse_eq]
  exact double_response_energy pOut pIn u v huv h

theorem original_intersectionResponse_energy (pOut : SelectedSupport 2 3)
    (pIn : SelectedSupport 2 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, OmittedUniformTwoInputPairSource.intersectionResponse pOut pIn
      (OmittedUniformTwoInputPairSource.uniformFirst pIn)
      (OmittedUniformTwoInputPairSource.uniformSecond pIn) h y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ x, h x ^ 2 :=
  double_intersectionResponse_energy pOut pIn _ _
    (OmittedUniformTwoInputPairSource.uniformFirst_ne_second pIn) h

end AESConcrete.OmittedUniformPairEventEnergy
