import AESConcrete.ActualMarkedUniform
import AESConcrete.MarkedBlockScale
import AESConcrete.MarkedBlockVanishing

/-!
# Actual marked-contraction code energy and its vanishing endpoints

The actual unit-code moment is combined with the exact shortened-source
normalization. Multiplication by q=256^4 leaves precisely 256^ell times
the code-moment bound. Both nonsurviving endpoints use actual response
cancellation, including uniform additive-map fibers in the full-image case.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualMarkedContractionEnergy
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg contractedResponse)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros uniformCount)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.ActualMarkedCodeMoment (Byte)

set_option maxRecDepth 100000

def zeta (ell d : ℕ) : ℝ := (256 : ℝ)^ell *
  ((MixedCodeMoment.byteMoment / 256)^min d (ell-d) *
    MixedCodeMoment.byteDelta^(ell-2*min d (ell-d)))

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
  have hcode := ActualMarkedCodeDual.actual_normalized_energy_bound
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

theorem actual_contracted_zero_of_nonsurviving_dimension
    (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hm : ∃ p, m p = true) (hout : ¬ (0 < d ∧ d < ell)) (y : Marked m → Byte) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
      (graphCoordinate (byteDiffusionHom inverse)) s y = 0 := by
  by_cases hd : d = 0
  · exact MarkedBlockVanishing.actual_contractedResponse_zero_of_high_zeros
      left right inverse m s hm (by omega) y
  · have hle : ell ≤ d := by omega
    exact ActualMarkedUniform.actual_contractedResponse_zero_of_uniform_image
      left right inverse m s hm (by omega) y

def dimension (m : GraphPosition → Bool) (s : Activity m → Bool) : ℕ :=
  4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))

/-- This endpoint theorem also covers more than four zero constraints,
where the truncated natural dimension is zero. -/
theorem actual_contracted_zero_outside_surviving
    (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hm : ∃ p, m p = true)
    (hout : ¬ (0 < dimension m s ∧ dimension m s < Fintype.card (Marked m)))
    (y : Marked m → Byte) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
      (graphCoordinate (byteDiffusionHom inverse)) s y = 0 := by
  by_cases hz : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s)
  · exact MarkedBlockVanishing.actual_contractedResponse_zero_of_high_zeros
      left right inverse m s hm hz y
  · apply actual_contracted_zero_of_nonsurviving_dimension left right inverse m s
      (dimension m s) (Fintype.card (Marked m)) rfl _ hm hout y
    dsimp only [dimension]
    omega

end AESConcrete.ActualMarkedContractionEnergy
