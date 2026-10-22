import AESConcrete.CoupledPairEventGeometry
import AESConcrete.ShortenedJointFourier
import AESConcrete.ThreeActivePlaneEnergy
import AESConcrete.ThreeActiveLineEnergy

/-!
# Raw response energies for the seven nonempty coupled-pair restrictions

Physical event geometry supplies the actual source, information masks,
translation family, pair projections and endpoint line. Every term retains the
same arbitrary signed JOINT residual-pair amplitude.

Single events use the actual two-sided Fourier word resources; double events
use the ordinary plane estimate; the triple endpoint uses the ordinary line
estimate and the INJECTIVE residual restriction's energy inequality. No
endpoint-zero claim, product amplitude or full-pair energy equality is used.
Uniform normalization, eight-term assembly and physical caps remain separate.

Constructive fixed independent-uniform-retained-key AES10/14/16, whitening,
omitted final MixColumns and ordered-distinct reference law remain fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledPairFiber (ResidualPositions RetainedPositions)
open AESConcrete.CoupledPairEventGeometry
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable

variable {pOut : SelectedSupport 3 4} {pIn : SelectedSupport 2 4}

/-- Raw counting response on the entire actual shortened physical code. -/
def rawEventResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventRetainedHom s) (fun c => h (eventResidualHom s c))

/-- The same raw restriction in the original labelled full-source domain. -/
def sourceEventResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (fun uv : EventSource s => retainedMap pOut pIn uv.val) (fun uv => h uv.val.1)

/-- Exact response equality, retaining all source points and the whole joint
amplitude. No weights, normalization or cardinality factor is introduced. -/
theorem sourceEventResponse_eq (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    sourceEventResponse s h = rawEventResponse s h := by
  funext y
  have he := (eventSourceEquiv s).sum_comp
    (fun c : EventCode s => h (eventResidualHom s c) *
      ∏ i : RetainedPositions pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (eventRetainedHom s c i))
  have hc (uv : EventSource s) (i : RetainedPositions pOut) :
      eventRetainedHom s (eventSourceEquiv s uv) i = retainedMap pOut pIn uv.val i := rfl
  simp_rw [eventSourceEquiv_residual, hc] at he
  exact he

/-- All single-event hypotheses are the actual physical masks/counts.
The raw joint source has q copies of its residual-pair energy. -/
theorem single_event_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have hsmall : s.val.card ≤ 2 := by omega
  have hdep : AES.maskSize (dependentMask s hsmall) = 1 := by
    rw [(dependentMask_spec s hsmall).1, hs]
  have he := ShortenedJointFourier.word_single_event_energy
    (outputZeroMask s) (inputZeroMask s) pOut.val.val.1 pIn.val.val.1
    (dependentMask s hsmall) (outputZeros_disjoint_retained s)
    (dependentMask_spec s hsmall).2 (inputZeros_disjoint_residual s)
    ((constraint_count s).trans hs) (ThreeActiveGeometry.retainedMask_size pOut)
    (CoupledPairFiber.residualMask_size pIn) hdep h
  exact he

/-- An arbitrary retained pair parameterizes every actual double-event
source point. The ordinary plane estimate uses its exact joint energy. -/
theorem pair_event_energy_at (s : Events pOut pIn) (hs : s.val.card = 2)
    (i : RetainedPositions pOut) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have he := ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (ThreeActiveGeometry.retainedCoordinates_card pOut) i (eventRetainedHom s)
    (fun c => h (eventResidualHom s c)) (pair_retained_projection_bijective s hs i)
  have henergy : (∑ c : EventCode s, h (eventResidualHom s c) ^ 2) = ∑ u, h u ^ 2 := by
    simpa only [hs, Nat.sub_self, pow_zero, one_mul] using
      eventCode_amplitude_energy s (by omega) h
  rw [henergy] at he
  exact he

theorem pair_event_energy (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (RetainedPositions pOut) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  exact pair_event_energy_at s hs (Classical.choice inferInstance) h

/-- The full three-event endpoint is an actual line. Its residual PAIR map
is injective; its energy is bounded by the full joint energy, never equated. -/
theorem triple_event_energy_at (s : Events pOut pIn) (hs : s.val.card = 3)
    (i : RetainedPositions pOut) (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  have he := ThreeActiveLineEnergy.word_line_energy_of_bijective
    (ThreeActiveGeometry.retainedCoordinates_card pOut) i (eventRetainedHom s)
    (fun c => h (eventResidualHom s c)) (triple_output_bijective s hs i)
  exact he.trans (mul_le_mul_of_nonneg_left (triple_code_amplitude_energy_le s hs h)
    (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)))

theorem triple_event_energy (s : Events pOut pIn) (hs : s.val.card = 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (RetainedPositions pOut) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  exact triple_event_energy_at s hs (Classical.choice inferInstance) h

theorem single_source_response_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤ (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact single_event_energy s hs h

theorem pair_source_response_energy (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤ (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact pair_event_energy s hs h

theorem triple_source_response_energy (s : Events pOut pIn) (hs : s.val.card = 3)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse s h y ^ 2) ≤ (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact triple_event_energy s hs h

end AESConcrete.CoupledPairEventEnergy
