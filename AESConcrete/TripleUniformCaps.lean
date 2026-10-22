import AESConcrete.TripleUniformMinorResponse
import AESConcrete.TripleUniformResponseEnergy

/-!
# actual selected-piece energy for the triple-uniform source

The four single, six pair and four triple conditional responses are identified
with their actual physical source restrictions before their energy estimates
are applied. All fourteen estimates retain one arbitrary signed amplitude and
the same original residual energy. Actual endpoint cancellation then supplies
the conditional fourteen-response adapter's remaining premises.

The normalized three-uniform source has exactly the amplitude's counting
energy. This identity and the actual selected-minor energy identity transfer
the response estimate to one selected (1,4) input and (3,4) output piece.
Physical support aggregation, operator conversion and inventory are separate.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference pairs and the fixed AES 10/14/16 target remain
unchanged. No physical (12,7) cap, inventory count, return or complete AES
theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformCaps
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource
open AESConcrete.TripleUniformFullResponse (SourceWord Retained residualKernel)
open AESConcrete.TripleUniformEventIndexing
open AESConcrete.TripleUniformMinorResponse (response)
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q s)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform nonzeroUniform_energy)

/-- One selected source/output piece, before physical support aggregation. -/
abbrev pieceSquaredBound : ℝ := TripleUniformResponseEnergy.C_safe

theorem pieceSquaredBound_eq :
    pieceSquaredBound = rho ^ 2 * kappa ^ 2 * (4 * q + 174 * s + 4) ^ 2 / (q - 1) ^ 4 := rfl

theorem pieceSquaredBound_nonneg : 0 ≤ pieceSquaredBound :=
  TripleUniformResponseEnergy.C_safe_nonneg

/-- Each original normalized uniform tuple has unit counting energy. -/
theorem uniform_tuple_energy (pIn : SelectedSupport 1 4) :
    (∑ v : SourceUniformPositions pIn → AES.Word,
      (∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) ^ 2) = 1 := by
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum
    (fun _ : SourceUniformPositions pIn => fun u : AES.Word => nonzeroUniform u ^ 2)]
  simp only [nonzeroUniform_energy AES.word_card_gt_one, Finset.prod_const_one]

/-- Exact normalization on the complete original four-word source, for signed h. -/
theorem source_energy_eq (pIn : SelectedSupport 1 4)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) :
    (∑ x, G x ^ 2) = ∑ u, h u ^ 2 := by
  rw [TripleUniformMinorResponse.full_source_sum pIn (fun x => G x ^ 2)]
  simp_rw [hsource, mul_pow]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, uniform_tuple_energy, mul_one]

theorem single_response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (i : Fin 4) :
    (∑ y, FourteenResponse.singleResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i y ^ 2) ≤
      (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  rw [singleResponses_eq_sourceEventResponse pOut pIn h i]
  exact TripleUniformEventEnergy.single_source_response_energy
    (singleEvents pOut pIn i) (singleEvents_card pOut pIn i) h

theorem pair_response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (i : Fin 6) :
    (∑ y, FourteenResponse.pairResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i y ^ 2) ≤
      (q * rho ^ 4 * kappa) * ∑ u, h u ^ 2 := by
  rw [pairResponses_eq_sourceEventResponse pOut pIn h i]
  exact TripleUniformEventEnergy.pair_source_response_energy
    (pairEvents pOut pIn i) (pairEvents_card pOut pIn i) h

theorem triple_response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (i : Fin 4) :
    (∑ y, FourteenResponse.tripleResponses (fun uv : SourceWord pIn => h uv.1)
      (residualKernel pOut pIn) (eventValue pOut pIn) i y ^ 2) ≤
      (rho ^ 2 * kappa ^ 2) * ∑ u, h u ^ 2 := by
  rw [tripleResponses_eq_sourceEventResponse pOut pIn h i]
  exact TripleUniformEventEnergy.triple_source_response_energy
    (tripleEvents pOut pIn i) (tripleEvents_card pOut pIn i) h

/-- Actual fourteen-response estimate, with no sign, zero or mean premise on h. -/
theorem response_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) :
    (∑ y, response pOut pIn h y ^ 2) ≤ pieceSquaredBound * ∑ u, h u ^ 2 := by
  exact TripleUniformResponseEnergy.conditional14_response_energy
    TripleUniformEventGeometry.word_card_real
    (fun uv : SourceWord pIn => h uv.1) (residualKernel pOut pIn)
    (eventValue pOut pIn) h
    (TripleUniformMinorResponse.rawFull_response_zero pOut pIn h)
    (TripleUniformMinorResponse.quadruple_events_zero_kernel pOut pIn)
    (single_response_energy pOut pIn h) (pair_response_energy pOut pIn h)
    (triple_response_energy pOut pIn h)

/-- The exact source and minor normalizations both precede this operator adapter. -/
theorem selected_source_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (G : AES.WordState → ℝ) (h : AES.Word → ℝ)
    (hsource : ∀ u v, G (source pIn u v) =
      h u * ∏ j : SourceUniformPositions pIn, nonzeroUniform (v j)) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut) G y ^ 2) ≤
      pieceSquaredBound * ∑ x, G x ^ 2 := by
  rw [TripleUniformMinorResponse.selectedStep_energy_eq pOut pIn G h hsource,
    source_energy_eq pIn G h hsource]
  exact response_energy pOut pIn h

/-- Canonical selected-piece interface, with the original component's energy. -/
theorem selected_piece_energy (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (f : AES.WordState → ℝ) :
    (∑ y, action (ActivityMinorInput.selectedStepKernel 3 4 pOut)
      (supportIndexComponent (0 : AES.Word) pIn.val f) y ^ 2) ≤
      pieceSquaredBound * ∑ x, supportIndexComponent (0 : AES.Word) pIn.val f x ^ 2 := by
  obtain ⟨h, _, _, hsource, _⟩ := word_source_representation pIn f
  exact selected_source_energy pOut pIn _ h hsource

end AESConcrete.TripleUniformCaps
