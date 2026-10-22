import AESConcrete.DoubleUniformPlaneGeometry
import AESConcrete.ThreeActiveLineEnergy

/-!
# All three double-zero line energies for the double-uniform source

The two mixed lines set one original uniform input and the omitted output to
zero. Their residual input and every retained output are bijective line
parameters, so the exact signed residual energy is preserved. The third line
sets both original uniform inputs to zero and is the actual residual axis. All
source values remain in the sums, including zero and arbitrary h(0).

Each line pays one residual operator factor and two residual column factors.
No response is asserted to vanish.
No physical cap or inventory extension is asserted. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct reference
pairs and fixed 10/14/16 remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformLineEnergy
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
open AESConcrete.DoubleUniformShortening
open AESConcrete.DoubleUniformPlaneGeometry

private theorem wordMixHom_apply (x : AES.WordState) :
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom x =
      WordCrossZero.wordMixAddEquiv x := rfl

/-- Both mixed double-zero lines retain the same signed one-word amplitude
and exactly its energy, rather than merely an injective subenergy. -/
theorem retained_sourceZeroOutputLine_energy_at
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j : SourceUniformPositions pIn) (s : MaskCoordinates pOut.val.val.1)
    (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (fun c : sourceZeroOutputLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom
          pIn (omittedLabel pOut) j =>
        sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 c.val.val)
      (fun c => h c.val.val.1) y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  have he := ThreeActiveLineEnergy.word_line_energy_of_bijective
    (retainedCoordinates_card pOut) s
    (fun c : sourceZeroOutputLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn (omittedLabel pOut) j =>
      sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 c.val.val)
    (fun c => h c.val.val.1)
    (sourceZeroOutputLine_output_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
      WordCrossZero.wordMixAddEquiv_zeroMDS pIn (omittedLabel pOut) j s.val
      (retained_ne_omitted pOut s))
  rw [sourceZeroOutputLine_residual_energy WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS pIn (omittedLabel pOut) j h] at he
  exact he

/-- Uniformly covers either original source-zero/omitted-zero line. -/
theorem retained_sourceZeroOutputLine_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (j : SourceUniformPositions pIn) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (fun c : sourceZeroOutputLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom
          pIn (omittedLabel pOut) j =>
        sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn pOut.val.val.1 c.val.val)
      (fun c => h c.val.val.1) y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact retained_sourceZeroOutputLine_energy_at pOut pIn j (Classical.choice inferInstance) h

/-- Both original uniform values are zero. The curve is the physical
residual input axis followed by actual word diffusion. -/
theorem retained_residualLine_energy_at
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3)
    (s : MaskCoordinates pOut.val.val.1) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (fun u : AES.Word => fun i : MaskCoordinates pOut.val.val.1 =>
        WordCrossZero.wordMixAddEquiv (Pi.single (residualLabel pIn) u) i.val) h y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  apply ThreeActiveLineEnergy.word_line_energy_of_bijective
    (retainedCoordinates_card pOut) s
    (fun u : AES.Word => fun i : MaskCoordinates pOut.val.val.1 =>
      WordCrossZero.wordMixAddEquiv (Pi.single (residualLabel pIn) u) i.val) h
  simpa only [source_residual_axis, wordMixHom_apply] using
    (residualLine_output_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
      WordCrossZero.wordMixAddEquiv_zeroMDS pIn s.val)

/-- Raw third double-zero line, including its zero source point. -/
theorem retained_residualLine_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (fun u : AES.Word => fun i : MaskCoordinates pOut.val.val.1 =>
        WordCrossZero.wordMixAddEquiv (Pi.single (residualLabel pIn) u) i.val) h y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  exact retained_residualLine_energy_at pOut pIn (Classical.choice inferInstance) h

/-- The same residual line in the original labelled full-source interface. -/
theorem retained_residualSource_energy
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 3) (h : AES.Word → ℝ) :
    (∑ y, IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
      (fun u : AES.Word => sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn pOut.val.val.1 (u, 0)) h y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  have hcurve : (fun u : AES.Word => sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
      pIn pOut.val.val.1 (u, 0)) =
      (fun u : AES.Word => fun i : MaskCoordinates pOut.val.val.1 =>
        WordCrossZero.wordMixAddEquiv (Pi.single (residualLabel pIn) u) i.val) := by
    funext u i
    change WordCrossZero.wordMixAddEquiv.toAddMonoidHom (source pIn u 0) i.val = _
    rw [source_residual_axis, wordMixHom_apply]
  rw [hcurve]
  exact retained_residualLine_energy pOut pIn h

end AESConcrete.DoubleUniformLineEnergy
