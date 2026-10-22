import AESConcrete.CoupledTripleResponseEnergy

/-!
# Selected support-component energy for the joint residual triple

The normalized minor and exact component energy transport the four-response
bound. Its two original nonzero-uniform weights have already been included.
Physical support aggregation is separate. Constructive independent-retained-
key AES10/14/16 scope.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.CoupledTripleCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

abbrev pieceSquaredBound : ℝ := CoupledTripleScalar.C3

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  CoupledTripleScalar.C3_nonneg

/-- A single arbitrary joint amplitude has exactly the component's energy. -/
theorem selected_piece_energy (pOut pIn : SelectedSupport 3 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hsource, henergy⟩ := CoupledTripleSource.word_source_representation pIn f
  rw [CoupledTripleMinorResponse.selectedStep_energy_eq pOut pIn _ h hsource, henergy]
  exact CoupledTripleResponseEnergy.response_energy pOut pIn h

end AESConcrete.CoupledTripleCaps
