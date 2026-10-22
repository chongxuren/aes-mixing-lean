import AESConcrete.CoupledPairResponseEnergy

/-!
# Selected support-component energy for the joint residual pair

The selected-minor identity and exact original support-component energy
transport the eight-response bound. Both original unit uniform input factors
have already been included. Physical support aggregation and the (12,10) step
cap remain separate. Fixed constructive independent-retained-key AES10/14/16
model.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledPairCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

abbrev pieceSquaredBound : ℝ := CoupledPairScalar.C_safe

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  CoupledPairScalar.C_safe_nonneg

/-- The full source representation supplies one joint amplitude with exactly
the original support-component energy, and the minor transport adds no factor. -/
theorem selected_piece_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 2 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hsource, henergy⟩ := CoupledPairSource.word_source_representation pIn f
  rw [CoupledPairMinorResponse.selectedStep_energy_eq pOut pIn _ h hsource, henergy]
  exact CoupledPairResponseEnergy.response_energy pOut pIn h

end AESConcrete.CoupledPairCaps
