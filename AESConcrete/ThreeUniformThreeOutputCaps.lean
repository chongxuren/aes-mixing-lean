import AESConcrete.ThreeUniformThreeOutputResponseEnergy

/-!
# Selected-component energy for (11,7)

The existing exact normalized-source representation supplies one arbitrary
signed residual-singleton amplitude and its counting energy. The response
bound already includes all three input uniform weights. Physical support
multiplicities and the unchanged certificate are separate. Constructive fixed
AES10/14/16 scope.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ThreeUniformThreeOutputCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WeightedThreeOutputGeometry (Residual)
open AESConcrete.WeightedThreeOutputCaps
  (normalizedSource normalizedSource_supported response_normalizedSource selectedStep_energy_eq)

private theorem counting_sum_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∑ x, f x) = (letI := b; ∑ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

abbrev pieceSquaredBound : ℝ := ThreeUniformThreeOutputScalar.C

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  ThreeUniformThreeOutputScalar.C_nonneg

theorem selected_normalizedSource_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (normalizedSource pIn h) y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  rw [selectedStep_energy_eq pOut pIn _ (normalizedSource_supported pIn h),
    response_normalizedSource pOut pIn h]
  exact ThreeUniformThreeOutputResponseEnergy.joint_response_energy pOut pIn h

theorem selected_piece_energy (pOut : SelectedSupport 3 3)
    (pIn : SelectedSupport 1 4) (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 3 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, hc, henergy⟩ := MultiUniformExpansion.supportIndexComponent_multi_uniform
    pIn.val AES.word_card_gt_one f
  rw [counting_sum_instances (X := Residual pIn → AES.Word) _ inferInstance] at henergy
  have ht := selected_normalizedSource_energy pOut pIn h
  rw [henergy, hc]
  exact ht

end AESConcrete.ThreeUniformThreeOutputCaps
