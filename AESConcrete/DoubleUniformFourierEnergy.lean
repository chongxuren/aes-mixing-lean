import AESConcrete.InvariantSubspaceFourier
import AESConcrete.DoubleUniformPlaneGeometry
import AESConcrete.WordFourierBounds
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Raw Fourier energies for the double-uniform source and single-zero planes

Both responses use the actual three retained physical labels and the same
arbitrary signed one-word amplitude. The full source has exactly q^2 copies of
that amplitude and a two-dimensional uniform translation subgroup. The
omitted-zero plane has exactly q copies and a one-dimensional correlated
uniform subgroup. Each original-input-zero plane also has q copies and its
remaining original uniform direction. Zero extension precedes the ambient
Fourier argument for every plane.

Only the actual ordinary two-sided Fourier residual resources are used. No
physical cap or inventory extension is asserted. Independent uniform retained
keys, whitening, omitted final MixColumns, ordered-distinct reference pairs
and fixed 10/14/16 stay unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformFourierEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.IndexedGraphEnergy
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
open AESConcrete.DoubleUniformShortening
open AESConcrete.DoubleUniformPlaneGeometry

/-- Exactly two unrestricted original uniform values accompany each residual
value. This is counting energy, before nonzero-uniform normalization. -/
theorem full_source_energy {V : Type*} [Fintype V]
    (p : SelectedSupport 1 3) (h : V → ℝ) :
    (∑ uv : V × (SourceUniformPositions p → V), h uv.1 ^ 2) =
      (Fintype.card V : ℝ) ^ 2 * ∑ u : V, h u ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    uniformTuple_card, Nat.cast_pow]
  exact (Finset.mul_sum _ _ _).symm

theorem word_card_real : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
  rw [AES.word_card]
  norm_num [ActivityCodeScalar.q]

/-- Adapter for the actual ordinary two-sided conjugate; no one-sided mixed
Fourier entry or column estimate is substituted. -/
theorem word_fourier_operator_energy (g : AES.Word → ℝ) :
    (∑ y, action (fourierConjugate WordFourierCore.wordPairing
      (residualMatrix AES.wordSuperboxKernel 0)) g y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * ∑ x, g x ^ 2 :=
  WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false g

theorem word_fourier_column_energy (v : AES.Word) :
    (∑ y, fourierConjugate WordFourierCore.wordPairing
      (residualMatrix AES.wordSuperboxKernel 0) y v ^ 2) ≤ UniformGraphScalar.kappa :=
  (WordFourierBounds.fourier_residual_column_energy_lt .ordinary .ordinary false v).le

/-- The full uniform plane determines both dependent Fourier coordinates.
Only the one remaining retained frequency pays an operator factor. -/
theorem retained_fullResponse_energy_at
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (retainedEquiv pOut pIn) (fun uv => h uv.1) y ^ 2) ≤
      (ActivityCodeScalar.q ^ 2 * UniformGraphScalar.rho ^ 2 *
        UniformGraphScalar.kappa ^ 2) * ∑ u, h u ^ 2 := by
  classical
  have hfree : Fintype.card
      (FreeCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i = s)) = 1 :=
    Fintype.card_subtype_eq s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i = s)) = 2 :=
    retained_other_card pOut s
  have hsurj : Function.Surjective
      (fun t : SourceUniformPositions pIn → AES.Word =>
        fun j : DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i = s) =>
          (retainedEquiv pOut pIn).toAddMonoidHom (0, t) j.val) :=
    (word_retained_uniform_pair_bijective pOut pIn s).surjective
  have hinv : ∀ (uv : AES.Word × (SourceUniformPositions pIn → AES.Word))
      (t : SourceUniformPositions pIn → AES.Word),
      h (uv + (0, t)).1 = h uv.1 := by
    intro uv t
    change h (uv.1 + 0) = h uv.1
    rw [add_zero]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : MaskCoordinates pOut.val.val.1 => i = s)
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy
    (retainedEquiv pOut pIn).toAddMonoidHom (retainedEquiv pOut pIn).injective
    (fun t : SourceUniformPositions pIn → AES.Word => (0, t)) hsurj
    (fun uv => h uv.1) hinv
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, full_source_energy, word_card_real] at he
  exact he.trans_eq (by ring)

/-- Raw full-source response on the actual retained triple. The signed
residual amplitude is unchanged, and the exact raw multiplicity is q^2. -/
theorem retained_fullResponse_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (retainedEquiv pOut pIn) (fun uv => h uv.1) y ^ 2) ≤
      (ActivityCodeScalar.q ^ 2 * UniformGraphScalar.rho ^ 2 *
        UniformGraphScalar.kappa ^ 2) * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact retained_fullResponse_energy_at pOut pIn (Classical.choice inferInstance) h

/-- The omitted-zero plane has one correlated uniform direction. Its
surjective retained singleton leaves two free Fourier operator factors. -/
theorem retained_zeroPlaneResponse_energy_at
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) (j : SourceUniformPositions pIn)
    (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (planeRetainedHom WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn (omittedLabel pOut) pOut.val.val.1)
      (planeAmplitude WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn (omittedLabel pOut) h) y ^ 2) ≤
      (ActivityCodeScalar.q * UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ u, h u ^ 2 := by
  classical
  let L := WordCrossZero.wordMixAddEquiv.toAddMonoidHom
  let z := omittedLabel pOut
  let E := planeRetainedHom L pIn z pOut.val.val.1
  let translations := uniformLineTranslation L pIn z
  have hfree : Fintype.card
      (FreeCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)) = 2 :=
    retained_other_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)) = 1 :=
    IndexedFourierSupport.dependentCoordinates_card s
  have hsurj : Function.Surjective
      (fun c : uniformLine L pIn z =>
        fun i : DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s) =>
          E (translations c) i.val) :=
    InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
      (fun c : uniformLine L pIn z => E (translations c))
      (retained_uniformLine_coordinate_bijective L WordCrossZero.wordMixAddEquiv_zeroMDS
        pOut pIn s).surjective
  have henergy : (∑ uv : zeroPlane L pIn z, planeAmplitude L pIn z h uv ^ 2) =
      ActivityCodeScalar.q * ∑ u, h u ^ 2 := by
    change (∑ uv : zeroPlane L pIn z, h uv.val.1 ^ 2) = _
    rw [zeroPlane_residual_energy L WordCrossZero.wordMixAddEquiv_zeroMDS pIn z j h,
      word_card_real]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy E
    (planeRetainedHom_injective L WordCrossZero.wordMixAddEquiv_zeroMDS
      pIn z pOut.val.val.1 (retainedMask_size pOut))
    translations hsurj (planeAmplitude L pIn z h) (planeAmplitude_translation L pIn z h)
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, henergy] at he
  exact he.trans_eq (by ring)

/-- Raw omitted-output-zero response, with no normalization and exactly q
copies of the same one-word signed residual energy. -/
theorem retained_zeroPlaneResponse_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (planeRetainedHom WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn (omittedLabel pOut) pOut.val.val.1)
      (planeAmplitude WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn (omittedLabel pOut) h) y ^ 2) ≤
      (ActivityCodeScalar.q * UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  haveI : Nonempty (SourceUniformPositions pIn) :=
    Fintype.card_pos_iff.mp (by rw [sourceUniformPositions_card]; norm_num)
  exact retained_zeroPlaneResponse_energy_at pOut pIn
    (Classical.choice inferInstance) (Classical.choice inferInstance) h

/-- Fixing either original uniform input at zero leaves one original uniform
translation direction and exactly q copies of the same signed amplitude. -/
theorem retained_sourceZeroPlaneResponse_energy_at
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j k : SourceUniformPositions pIn) (hkj : k ≠ j)
    (s : MaskCoordinates pOut.val.val.1) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (sourceZeroPlaneRetainedHom WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn j pOut.val.val.1)
      (fun uv => h uv.val.1) y ^ 2) ≤
      (ActivityCodeScalar.q * UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ u, h u ^ 2 := by
  classical
  let L := WordCrossZero.wordMixAddEquiv.toAddMonoidHom
  let E := sourceZeroPlaneRetainedHom L pIn j pOut.val.val.1
  let translations := sourceZeroPlaneTranslation L WordCrossZero.wordMixAddEquiv_zeroMDS
    pIn j k hkj
  have hfree : Fintype.card
      (FreeCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)) = 2 :=
    retained_other_card pOut s
  have hdep : Fintype.card
      (DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)) = 1 :=
    IndexedFourierSupport.dependentCoordinates_card s
  have hsurj : Function.Surjective
      (fun t : AES.Word =>
        fun i : DependentCoordinates (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s) =>
          E (translations t) i.val) :=
    InvariantSubspaceFourier.dependent_projection_surjective_of_coordinate s
      (fun t : AES.Word => E (translations t))
      (sourceZeroPlaneTranslation_output_bijective L WordCrossZero.wordMixAddEquiv_zeroMDS
        pIn j k hkj s.val).surjective
  have henergy : (∑ uv : sourceZeroPlane (V := AES.Word) pIn j, h uv.val.1 ^ 2) =
      ActivityCodeScalar.q * ∑ u, h u ^ 2 := by
    rw [sourceZeroPlane_residual_energy L WordCrossZero.wordMixAddEquiv_zeroMDS
      pIn j k hkj h, word_card_real]
  have he := InvariantSubspaceFourier.response_uniform_energy
    WordFourierCore.wordPairing word_add_self (residualMatrix AES.wordSuperboxKernel 0)
    (fun i : MaskCoordinates pOut.val.val.1 => i ≠ s)
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
    word_fourier_operator_energy word_fourier_column_energy E
    (sourceZeroPlaneRetainedHom_injective L WordCrossZero.wordMixAddEquiv_zeroMDS
      pIn j pOut.val.val.1 (retainedMask_size pOut))
    translations hsurj (fun uv => h uv.val.1)
    (sourceZeroPlaneAmplitude_translation L WordCrossZero.wordMixAddEquiv_zeroMDS
      pIn j k hkj h)
  simp only [← Nat.card_eq_fintype_card] at he hfree hdep
  rw [hfree, hdep, henergy] at he
  exact he.trans_eq (by ring)

/-- Either physical source-zero plane receives the same raw coefficient.
Choosing the other original uniform label is only an information-set proof;
the response and signed amplitude do not depend on this choice. -/
theorem retained_sourceZeroPlaneResponse_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (sourceZeroPlaneRetainedHom WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn j pOut.val.val.1)
      (fun uv => h uv.val.1) y ^ 2) ≤
      (ActivityCodeScalar.q * UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa) *
        ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  have hc : Fintype.card {k : SourceUniformPositions pIn // k ≠ j} = 1 := by
    rw [Fintype.card_subtype_compl (fun k : SourceUniformPositions pIn => k = j),
      Fintype.card_subtype_eq, sourceUniformPositions_card]
  haveI : Nonempty {k : SourceUniformPositions pIn // k ≠ j} :=
    Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  let k : {k : SourceUniformPositions pIn // k ≠ j} := Classical.choice inferInstance
  exact retained_sourceZeroPlaneResponse_energy_at pOut pIn j k.val k.property
    (Classical.choice inferInstance) h

end AESConcrete.DoubleUniformFourierEnergy
