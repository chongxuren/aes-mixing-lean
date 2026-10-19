import AESConcrete.ActualRestrictedDensity
import AESConcrete.ActualRestrictedResponse

/-!
# Restricted responses of the actual AES column

Both branches use the actual first byte-channel product and the actual
forward/inverse diffusion. An arbitrary event remains an unnormalized
restriction on the shortened source. The only premises describe coordinate
sets and the input zero pattern; no density, MDS, tensor norm or column
energy bound is assumed. The two branches still need support aggregation
before they imply a complete multibyte word-column bound.

Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualRestrictedColumnResponse
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word tensorResponse)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ActualRestrictedDensity (restrictedSource outputCoordinates)

/-- Few observed coordinates: the nonnegative marginal is bounded before
the signed residual operator is applied. -/
theorem low_observed_energy (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u out : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (o : MaskCoordinates out → Orientation) :
    (∑ y : MaskCoordinates out → Byte,
      tensorResponse (fun i => residualMatrix (channel (o i)) 0)
        (outputCoordinates inverse r z out) (restrictedSource right inverse a r z event) y ^ 2) ≤
      ((1 : ℝ)/64)^(2*maskSize r) *
        (((65 : ℝ)/8192) * ((9 : ℝ)/128)^2)^maskSize out := by
  rw [ActualRestrictedResponse.tensorResponse_eq_action_marginal]
  have hm := ActualRestrictedDensity.restrictedSource_marginal_energy_le
    right inverse a r z s u out hsu hzu hsize hr hobs ha event
  have ht := FiniteTensorEnergy.actual_byte_residual_coordinate_energy o
    (RestrictedMarginalEnergy.marginal (outputCoordinates inverse r z out)
      (restrictedSource right inverse a r z event))
  rw [maskCoordinates_card] at ht
  calc
    _ ≤ ((9 : ℝ)/128)^(2*maskSize out) *
        ∑ y : MaskCoordinates out → Byte,
          RestrictedMarginalEnergy.marginal (outputCoordinates inverse r z out)
            (restrictedSource right inverse a r z event) y^2 := ht
    _ ≤ ((9 : ℝ)/128)^(2*maskSize out) *
        (((1 : ℝ)/64)^(2*maskSize r) * ((65 : ℝ)/8192)^maskSize out) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [mul_pow, pow_mul]; ring

/-- Enough observed coordinates: the core marked outputs form an actual
information set; every additional residual output pays its column energy. -/
theorem high_observed_energy (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u core extra : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r core)
    (hcore : maskSize r + maskSize z + maskSize core = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (o : MaskCoordinates core → Orientation) (p : MaskCoordinates extra → Orientation) :
    (∑ y : (MaskCoordinates core ⊕ MaskCoordinates extra) → Byte,
      tensorResponse (Sum.elim (fun i => residualMatrix (channel (o i)) 0)
          (fun i => residualMatrix (channel (p i)) 0))
        (fun c => Sum.elim (outputCoordinates inverse r z core c)
          (outputCoordinates inverse r z extra c))
        (restrictedSource right inverse a r z event) y ^ 2) ≤
      ((1 : ℝ)/64)^(2*maskSize r) *
        (((65 : ℝ)/8192) * ((9 : ℝ)/128)^2)^maskSize core *
          ((8383 : ℝ)/2088960)^maskSize extra := by
  let e : ShortenedGraph (byteDiffusionHom inverse) r z ≃ (MaskCoordinates core → Byte) :=
    Equiv.ofBijective (outputCoordinates inverse r z core)
      (RestrictedMDSCoordinates.actual_output_projection_bijective inverse r z core hr hcore)
  have hsource := ActualRestrictedDensity.restrictedSource_energy_le
    right inverse a r z s u hsu hzu hsize ha event
  have h := ActualRestrictedResponse.actual_split_response_energy_of_source_bound
    o p e (outputCoordinates inverse r z extra) (restrictedSource right inverse a r z event)
    (((1 : ℝ)/64)^(2*maskSize r) * ((65 : ℝ)/8192)^(maskSize s+maskSize u)) hsource
  have hd : maskSize s + maskSize u = maskSize core := by omega
  have hc : (16766/4177920 : ℝ) = 8383/2088960 := by norm_num
  rw [maskCoordinates_card, maskCoordinates_card, hd, hc] at h
  change (∑ y : (MaskCoordinates core ⊕ MaskCoordinates extra) → Byte,
    tensorResponse (Sum.elim (fun i => residualMatrix (channel (o i)) 0)
        (fun i => residualMatrix (channel (p i)) 0))
      (fun c => Sum.elim (outputCoordinates inverse r z core c)
        (outputCoordinates inverse r z extra c))
      (restrictedSource right inverse a r z event) y^2) ≤ _ at h
  calc
    _ ≤ _ := h
    _ = _ := by rw [mul_pow, pow_mul]; ring

end AESConcrete.ActualRestrictedColumnResponse
