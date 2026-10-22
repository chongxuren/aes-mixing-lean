import AESConcrete.TwoOmittedOutputRawGeometry
import AESConcrete.IndexedTripleEnergy
import AESConcrete.WordMixedCentering

/-!
# Raw two-output response cancellation before the two input uniforms

The original residual input and both retained outputs parametrize the actual
input-zero Code with no output zeros. The bare response factors into the sum
of an arbitrary signed original amplitude and two actual residual row sums. It
therefore vanishes without any condition on h(0) or the sum of h.

This response has no input uniform weight and no omitted-output uniform
weight. The original singleton input zero Z is part of Code throughout. It is
not identified with the actual selected minor, whose weight-dependent analysis
belongs to separate components.

Fixed constructive AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

No weighted-response bound, physical cap or certificate is claimed here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoOmittedOutputRawResponse
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOutputRawGeometry

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

/-- The two actual residual factors, before all input and output uniform weights. -/
def bareKernel (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (y : Retained pOut → AES.Word) (c : Code pOut pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn c i)

def bareResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (curve pOut pIn) (fun c => h (residualTuple pOut pIn c)) y

theorem bareResponse_eq_sum (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    bareResponse pOut pIn h y =
      ∑ c : Code pOut pIn, h (residualTuple pOut pIn c) * bareKernel pOut pIn y c := rfl

/-- Exact finite factorization; no amplitude cancellation is assumed. -/
theorem bareResponse_factorization
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    bareResponse pOut pIn h y = (∑ u, h u) *
      ∑ x : Retained pOut → AES.Word, ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (x i) := by
  unfold bareResponse IndexedTripleEnergy.response
  rw [← Equiv.sum_comp (residualRetainedEquiv pOut pIn).symm
    (fun c : Code pOut pIn => h (residualTuple pOut pIn c) * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (curve pOut pIn c i))]
  rw [Fintype.sum_prod_type]
  simp_rw [residualRetainedEquiv_symm_residual, residualRetainedEquiv_symm_curve]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  exact (Finset.mul_sum _ _ _).symm

theorem retainedResidual_sum_zero (pOut : SelectedSupport 2 4)
    (y : Retained pOut → AES.Word) :
    (∑ x : Retained pOut → AES.Word, ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (x i)) = 0 := by
  rw [← Fintype.prod_sum
    (fun i : Retained pOut => fun v : AES.Word => residualMatrix AES.wordSuperboxKernel 0 (y i) v)]
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact WordMixedCentering.residual_row_sum AES.wordSuperboxKernel
    AES.word_superbox_pointed (y i)

/-- Kernel row sums kill the bare response for every signed original h, including h(0). -/
theorem bareResponse_zero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    bareResponse pOut pIn h y = 0 := by
  rw [bareResponse_factorization, retainedResidual_sum_zero, mul_zero]

theorem bareResponse_eq_zero (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 3)
    (h : (Residual pIn → AES.Word) → ℝ) : bareResponse pOut pIn h = 0 := by
  funext y
  exact bareResponse_zero pOut pIn h y

end AESConcrete.TwoOmittedOutputRawResponse
