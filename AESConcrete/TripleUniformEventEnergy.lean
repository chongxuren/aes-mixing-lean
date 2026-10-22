import AESConcrete.TripleUniformEventGeometry
import AESConcrete.DoubleUniformFourierEnergy
import AESConcrete.ThreeActiveLineEnergy

/-!
# actual energies of the fourteen proper restrictions

Physical event geometry supplies every information-set and translation
premise. Single and pair restrictions use the ordinary two-sided Fourier
residual resources. Triple restrictions use the stronger ordinary line
estimate. All terms retain the same arbitrary signed amplitude, including its
zero value.

No selected-minor identity, physical cap, inventory addition or complete AES
theorem is asserted. Independent retained keys, whitening, omitted final
MixColumns, ordered-distinct reference pairs and the fixed AES 10/14/16 target
remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource (residualLabel source_residual)
open AESConcrete.TripleUniformFullResponse (Retained retainedMap)
open AESConcrete.TripleUniformEventGeometry
open AESConcrete.ThreeActiveGeometry (retainedMask_size retainedCoordinates_card)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.UniformGraphScalar (rho kappa kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable

variable {pOut : SelectedSupport 3 4} {pIn : SelectedSupport 1 4}

/-- The raw response on the actual shortened physical code. -/
def rawEventResponse (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventRetainedHom s) (fun c => h (c.val (residualLabel pIn)))

/-- Same response in the original labelled source restriction. -/
def sourceEventResponse (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    (Retained pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (fun uv : EventSource s => retainedMap pOut pIn uv.val) (fun uv => h uv.val.1)

theorem sourceEventResponse_eq (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    sourceEventResponse s h = rawEventResponse s h := by
  funext y
  have he := Equiv.sum_comp (eventSourceEquiv s)
    (fun c : EventCode s => h (c.val (residualLabel pIn)) *
      ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (eventRetainedHom s c i))
  have ha (uv : EventSource s) :
      (eventSourceEquiv s uv).val (residualLabel pIn) = uv.val.1 :=
    source_residual pIn uv.val.1 uv.val.2
  have hc (uv : EventSource s) (i : Retained pOut) :
      eventRetainedHom s (eventSourceEquiv s uv) i = retainedMap pOut pIn uv.val i := by
    rw [eventRetainedHom_apply]
    rfl
  simp_rw [ha, hc] at he
  exact he

/-- All geometry and compatible Fourier resources are instantiated here.
At three restrictions this generic estimate is rho^6, not the ordinary line cap. -/
theorem rawEvent_fourier_energy (s : ProperEvents pOut pIn) (h : AES.Word → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤
      (rho ^ (3 - (3 - s.val.card))) ^ 2 * kappa ^ (3 - s.val.card) *
        (q ^ (3 - s.val.card) * ∑ u, h u ^ 2) := by
  classical
  have he := ShortenedWeightedFourier.response_uniform_energy
    wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
    (outputZeroMask s) (inputZeroMask s) pOut.val.val.1
    (informationMask s) (dependentMask s) (residualLabel pIn)
    (informationMask_disjoint s) (informationMask_spec s).2 (information_size_identity s)
    (dependentMask_disjoint s) (dependentMask_spec s).2 (residual_not_inputZero s)
    (dependent_size_identity s)
    (ShortenedWeightedFourier.physicalFree pOut.val.val.1 (dependentMask s))
    (ShortenedWeightedFourier.physicalFree_complement _ _)
    WordFourierCore.wordPairing AESMixing.word_add_self
    (residualMatrix AES.wordSuperboxKernel 0) rho kappa kappa_nonneg
    DoubleUniformFourierEnergy.word_fourier_operator_energy
    DoubleUniformFourierEnergy.word_fourier_column_energy h
  rw [retainedMask_size pOut, (dependentMask_spec s).1, word_card_real] at he
  exact he

theorem single_event_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 1)
    (h : AES.Word → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have he := rawEvent_fourier_energy s h
  norm_num only [hs] at he
  exact he.trans_eq (by ring)

theorem pair_event_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 2)
    (h : AES.Word → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have he := rawEvent_fourier_energy s h
  norm_num only [hs] at he
  exact he.trans_eq (by ring)

/-- A triple event gives a genuine ordinary line; its residual energy is
exactly sum h^2, and a retained coordinate is an actual bijective parameter. -/
theorem triple_event_energy_at (s : ProperEvents pOut pIn) (hs : s.val.card = 3)
    (i : Retained pOut) (h : AES.Word → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ rho ^ 2 * kappa ^ 2 * ∑ u, h u ^ 2 := by
  have hp : Function.Bijective (fun c : EventCode s => eventRetainedHom s c i) := by
    simpa only [eventRetainedHom_apply] using triple_output_bijective s hs i
  have he := ThreeActiveLineEnergy.word_line_energy_of_bijective
    (retainedCoordinates_card pOut) i (eventRetainedHom s)
    (fun c => h (c.val (residualLabel pIn))) hp
  rw [eventCode_amplitude_energy s h, hs] at he
  simpa only [rawEventResponse, Nat.sub_self, pow_zero, one_mul] using he

theorem triple_event_energy (s : ProperEvents pOut pIn) (hs : s.val.card = 3)
    (h : AES.Word → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ rho ^ 2 * kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact triple_event_energy_at s hs (Classical.choice inferInstance) h

theorem single_source_response_energy (s : ProperEvents pOut pIn)
    (hs : s.val.card = 1) (h : AES.Word → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact single_event_energy s hs h

theorem pair_source_response_energy (s : ProperEvents pOut pIn)
    (hs : s.val.card = 2) (h : AES.Word → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact pair_event_energy s hs h

theorem triple_source_response_energy (s : ProperEvents pOut pIn)
    (hs : s.val.card = 3) (h : AES.Word → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤ rho ^ 2 * kappa ^ 2 * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact triple_event_energy s hs h

end AESConcrete.TripleUniformEventEnergy
