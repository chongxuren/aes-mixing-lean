import AESConcrete.SingletonResidualCore
import AESConcrete.SingletonResidualGeometry
import AESConcrete.ActivityMinorInput

/-!
# Actual selected `(3,4)` output on a singleton residual input

Geometry identifies the original physical source and output coordinates. The
analytic graph estimate is then applied to the same arbitrary signed
amplitude, with exactly its original counting energy. No normalized code
indicator, independent-coordinate model or extra source factor is used.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and fixed 10/14/16 are preserved. This source adds no
cap or inventory entry. Physical aggregation and scalar comparison are
separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SingletonResidualEnergy
open AESMixing
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction
open AESConcrete.ActivityMinorInput (selectedStepKernel selectedStepKernel_action)
open AESConcrete.SingletonResidualCore
open AESConcrete.SingletonResidualGeometry
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

/-- Exact rectangular kernel on the actual code, in the explicit retained
output coordinate equivalence. This equality is before any energy bound. -/
theorem minorKernel_point (p : SelectedSupport 3 4) (U : Fin 16)
    (hU : AES.maskSize U = 1)
    (y : {i : Fin 4 // selectedRetained 3 4 p i} → AES.Word) (v : AES.Word) :
    minorKernel (selectedRetained 3 4 p) (fun _ => wordResidual)
      (nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p))
      y (point U hU (retainedBase p) v) =
      nonzeroUniform (omittedMap p U hU v) *
        wordTripleGraphKernel (retainedPairMap p U hU)
          (retainedOutputEquiv p y) v := by
  have hbase : point U hU (retainedBase p) v (retainedLabels p 2).val = v :=
    point_base U hU (retainedBase p) v
  unfold minorKernel
  rw [retained_prod p (fun i =>
    wordResidual (y i) (point U hU (retainedBase p) v i.val))]
  rw [omitted_prod p (fun i =>
    nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p) i
      (point U hU (retainedBase p) v i.val))]
  simp only [nonzeroWeight, selectedZeros_empty, if_false]
  rw [hbase]
  dsimp [wordTripleGraphKernel, GraphColumnEnergy.graphKernel, tensorKernel,
    retainedPairMap, retainedOutputEquiv, omittedMap, omittedLabel]
  ring

/-- The actual selected response has the graph-kernel action with the
same signed source amplitude; the source zero is retained in the sum. -/
theorem selected_minor_response_graph (p : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 1) (f : AES.WordState → ℝ)
    (y : {i : Fin 4 // selectedRetained 3 4 p i} → AES.Word) :
    minorResponse (selectedRetained 3 4 p) (fun _ => wordResidual)
      (nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p))
      (selectedPullback pIn f) y =
      action (wordTripleGraphKernel
        (retainedPairMap p (activeMask pIn) (activeMask_size pIn)))
        (fun v => nonzeroUniform (omittedMap p (activeMask pIn) (activeMask_size pIn) v) *
          selectedAmplitude pIn (retainedBase p) f v)
        (retainedOutputEquiv p y) := by
  unfold minorResponse
  rw [selected_action_reindex pIn (retainedBase p) f]
  unfold action
  apply Finset.sum_congr rfl
  intro v _
  rw [minorKernel_point]
  ring

/-- Arbitrary-signed-input selected-piece energy for the actual `(12,4)`
route. The sole omitted input weight contributes `1/(q-1)` once. -/
theorem selected_piece_energy (p : SelectedSupport 3 4)
    (pIn : SelectedSupport 1 1) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 p)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      (((21 / 131072 : ℝ) ^ 2 * (2 / (15 * 4294967296) : ℝ) ^ 2) /
        ((4294967296 : ℝ) - 1)) *
          ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  rw [selectedStepKernel_action, selectedWordTensor_minor_energy]
  change (∑ y, minorResponse (selectedRetained 3 4 p) (fun _ => wordResidual)
    (nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p))
    (selectedPullback pIn f) y ^ 2) ≤ _
  have he := word_response_energy (retainedOutputEquiv p)
    (retainedPairMap p (activeMask pIn) (activeMask_size pIn))
    (omittedMap p (activeMask pIn) (activeMask_size pIn))
    (selectedAmplitude pIn (retainedBase p) f)
    (minorResponse (selectedRetained 3 4 p) (fun _ => wordResidual)
      (nonzeroWeight (selectedRetained 3 4 p) (selectedZeros 3 4 p))
      (selectedPullback pIn f))
    (selected_minor_response_graph p pIn f)
  rw [selectedAmplitude_energy] at he
  simpa only [UniformGraphScalar.rho, UniformGraphScalar.kappa, ActivityCodeScalar.q] using he

end AESConcrete.SingletonResidualEnergy
