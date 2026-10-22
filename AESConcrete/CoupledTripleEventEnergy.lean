import AESConcrete.CoupledTripleEventGeometry
import AESConcrete.FiniteTensorEnergy
import AESConcrete.ThreeActivePlaneEnergy

/-!
# Raw energies for the three nonempty joint-triple restrictions

The two singleton events project bijectively to the retained and residual
triples. Three ordinary word operators therefore give rho^6 against the same
arbitrary signed joint h. The intersection is an actual plane: its retained
pair projection is bijective, but its residual triple map is only injective.
Its coefficient rho^4*kappa uses subenergy, never an equality with full h.

Source geometry, these raw estimates, normalized response assembly and
physical support aggregation have separate roles. No factorization, endpoint
vanishing or orthogonality of signed responses is assumed. Constructive
AES10/14/16 with independent uniform retained keys, whitening, omitted final
MixColumns and ordered-distinct reference pairs remains fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleEventEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.CoupledTripleFiber (ResidualPositions RetainedPositions)
open AESConcrete.CoupledTripleEventGeometry
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)

attribute [local instance] Classical.propDecidable

variable {pOut pIn : SelectedSupport 3 4}

/-- Unnormalized counting response on the actual shortened physical code. -/
def rawEventResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (eventRetainedHom s) (fun c => h (eventResidualHom s c))

/-- The same response in its original full-source labels. -/
def sourceEventResponse (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (RetainedPositions pOut → AES.Word) → ℝ :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
    (fun uv : EventSource s => eventRetainedHom s (eventSourceEquiv s uv))
    (fun uv => h uv.val.1)

/-- The full source/code equivalence introduces no weight or multiplicity. -/
theorem sourceEventResponse_eq (s : Events pOut pIn)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    sourceEventResponse s h = rawEventResponse s h := by
  funext y
  have he := Equiv.sum_comp (eventSourceEquiv s)
    (fun c => h (eventResidualHom s c) *
      ∏ i : RetainedPositions pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (eventRetainedHom s c i))
  simp_rw [eventSourceEquiv_residual] at he
  exact he

/-- A singleton retained triple is a full coordinate input to three operators.
The simultaneous residual bijection preserves the original joint energy. -/
theorem single_event_energy (s : Events pOut pIn) (hs : s.val.card = 1)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤ rho ^ 6 * ∑ u, h u ^ 2 := by
  classical
  let e : EventCode s ≃ (RetainedPositions pOut → AES.Word) :=
    Equiv.ofBijective (eventRetainedHom s) (single_retained_bijective s hs)
  let g : (RetainedPositions pOut → AES.Word) → ℝ :=
    fun x => h (eventResidualHom s (e.symm x))
  have hr : rawEventResponse s h =
      action (coordinateKernel (fun _ : RetainedPositions pOut =>
        residualMatrix AES.wordSuperboxKernel 0)) g := by
    funext y
    calc
      _ = ∑ x : RetainedPositions pOut → AES.Word,
          h (eventResidualHom s (e.symm x)) *
            ∏ i : RetainedPositions pOut,
              residualMatrix AES.wordSuperboxKernel 0 (y i)
                (eventRetainedHom s (e.symm x) i) :=
        (Equiv.sum_comp e.symm (fun c => h (eventResidualHom s c) *
          ∏ i : RetainedPositions pOut,
            residualMatrix AES.wordSuperboxKernel 0 (y i) (eventRetainedHom s c i))).symm
      _ = _ := by
        change _ = ∑ x, (∏ i : RetainedPositions pOut,
          residualMatrix AES.wordSuperboxKernel 0 (y i) (x i)) *
            h (eventResidualHom s (e.symm x))
        apply Finset.sum_congr rfl
        intro x _
        have hx : eventRetainedHom s (e.symm x) = x := e.apply_symm_apply x
        rw [hx]
        exact mul_comm _ _
  have hg : (∑ x, g x ^ 2) = ∑ u, h u ^ 2 := by
    calc
      _ = ∑ c : EventCode s, h (eventResidualHom s c) ^ 2 :=
        Equiv.sum_comp e.symm (fun c => h (eventResidualHom s c) ^ 2)
      _ = _ := single_code_amplitude_energy s hs h
  rw [hr]
  have he := FiniteTensorEnergy.uniform_coordinate_energy
    (residualMatrix AES.wordSuperboxKernel 0) rho
    SharpDampedWordNorm.word_superbox_residual_energy g
  simpa only [ThreeActiveGeometry.retainedCoordinates_card,
    show 2 * 3 = 6 by decide, hg] using he

/-- The surviving intersection has an actual retained-pair information set. -/
theorem double_event_energy_at (s : Events pOut pIn) (hs : s.val.card = 2)
    (i : RetainedPositions pOut)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  have he := ThreeActivePlaneEnergy.word_plane_energy_of_bijective
    (ThreeActiveGeometry.retainedCoordinates_card pOut) i (eventRetainedHom s)
    (fun c => h (eventResidualHom s c)) (double_retained_projection_bijective s hs i)
  exact he.trans (mul_le_mul_of_nonneg_left
    (double_code_amplitude_energy_le s hs h)
    (mul_nonneg (pow_nonneg rho_nonneg _) kappa_nonneg))

/-- No retained-label choice remains in the public intersection estimate. -/
theorem double_event_energy (s : Events pOut pIn) (hs : s.val.card = 2)
    (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, rawEventResponse s h y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (RetainedPositions pOut) :=
    Fintype.card_pos_iff.mp (by
      rw [ThreeActiveGeometry.retainedCoordinates_card]
      norm_num)
  exact double_event_energy_at s hs (Classical.choice inferInstance) h

theorem input_event_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse (inputEvent pOut pIn) h y ^ 2) ≤
      rho ^ 6 * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact single_event_energy _ (inputEvent_card pOut pIn) h

theorem output_event_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse (outputEvent pOut pIn) h y ^ 2) ≤
      rho ^ 6 * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact single_event_energy _ (outputEvent_card pOut pIn) h

theorem intersection_event_energy (h : (ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, sourceEventResponse (intersectionEvent pOut pIn) h y ^ 2) ≤
      (rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [sourceEventResponse_eq]
  exact double_event_energy _ (intersectionEvent_card pOut pIn) h

end AESConcrete.CoupledTripleEventEnergy
