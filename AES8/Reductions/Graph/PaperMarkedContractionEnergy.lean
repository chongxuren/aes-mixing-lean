import AES8.Reductions.Graph.PaperMarkedCodeEnergy
import AESConcrete.ActualMarkedContractionEnergy

/-!
# Exact normalization of the printed-route marked-code energy

Module role: convert normalized unit-code energy to physical contraction
energy with the original source cardinality and frame factors. The scalar
zeta and exact normalization identity are unchanged. Vanishing identities
remain separate and are reused by the frame consumer. Source candidate only;
no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperMarkedContractionEnergy
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg contractedResponse)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros uniformCount)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.ActualMarkedCodeMoment (Byte)
open AESConcrete.ActualMarkedContractionEnergy (zeta)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual graph/source/frame normalization supplies every scale factor. -/
theorem actual_contracted_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    (4294967296 : ℝ) * (∑ y : Marked m → Byte,
      contractedResponse m (markedLeg (channel left) (channel right) m)
        (graphCoordinate (byteDiffusionHom inverse)) s y^2) ≤ zeta ell d := by
  let coeff : ℝ :=
    Real.sqrt (Fintype.card (ShortenedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s))) /
      (16 : ℝ)^uniformCount s
  have hresponse (y : Marked m → Byte) :
      contractedResponse m (markedLeg (channel left) (channel right) m)
        (graphCoordinate (byteDiffusionHom inverse)) s y =
        coeff * MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
          (sourceCoordinates (byteDiffusionHom inverse) m s) y := by
    exact MarkedBlockShortening.contractedResponse_normalized
      (by norm_num [BinaryWord.card]) _ _ _ _ _
  have henergy :
      (∑ y : Marked m → Byte,
        contractedResponse m (markedLeg (channel left) (channel right) m)
          (graphCoordinate (byteDiffusionHom inverse)) s y^2) =
        coeff^2 * ∑ y : Marked m → Byte,
          MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
            (sourceCoordinates (byteDiffusionHom inverse) m s) y^2 := by
    simp_rw [hresponse, mul_pow]
    exact (Finset.mul_sum _ _ _).symm
  have hscale : (256 : ℝ)^4 * coeff^2 = (256 : ℝ)^ell := by
    simpa only [coeff, hlen] using MarkedBlockScale.normalization_scale
      (by norm_num [BinaryWord.card]) (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      m s (by omega)
  have hcode := AES8.PaperMarkedCodeEnergy.actual_normalized_energy_bound
    left right inverse m s d ell hlen hdim hdle
  unfold zeta
  calc
    _ = ((256 : ℝ)^4 * coeff^2) * ∑ y : Marked m → Byte,
        MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
          (sourceCoordinates (byteDiffusionHom inverse) m s) y^2 := by
      rw [henergy, show (4294967296 : ℝ) = (256 : ℝ)^4 by norm_num]
      ring
    _ = (256 : ℝ)^ell * ∑ y : Marked m → Byte,
        MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
          (sourceCoordinates (byteDiffusionHom inverse) m s) y^2 := by rw [hscale]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcode (by positivity)


#print axioms actual_contracted_energy_le
end AES8.PaperMarkedContractionEnergy
