import AESPaper.WordMarkedDual

/-!
# Exact Fourier transport of damped word-code vectors

This is a vector identity, rather than only equality of total energies.
It retains an independently fixed kernel on every physical marked leg.
The actual word specialization toggles Fourier flags and preserves adjoint
flags, including the transposed input legs. Rectangular operator transport
and quantitative operator bounds are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordCodeFourier
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WordMarkedCode (markedCode normalized_source_eq_code)
attribute [local instance] Classical.propDecidable

section GenericCode
variable {K V : Type*} [Fintype K] [DecidableEq K] [AddCommGroup V] [Fintype V]

/-- Product Fourier transports the full damped unit-code vector to the
damped unit indicator of its actual trace-character annihilator. -/
theorem code_fourier (B : CharacterPairing V) (hchar : ∀ x : V, x+x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) [Fintype C] :
    action (pairingFourier (B.product K))
        (action (coordinateKernel T) (unitSubgroupIndicator C)) =
      action (coordinateKernel (fun k => fourierConjugate B (T k)))
        (unitSubgroupIndicator ((B.product K).annihilator C)) := by
  have hp : ∀ x : K → V, x+x = 0 := by
    intro x
    funext k
    exact hchar (x k)
  symm
  rw [← MixedCodeMoment.coordinate_fourierConjugate,
    ← pairingFourier_subgroup (B.product K) C]
  unfold fourierConjugate
  rw [kernelCompose_action, kernelCompose_action,
    pairingFourier_twice (B.product K) hp]

end GenericCode

section WordCode
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Whole-word Fourier toggles each local Fourier flag while retaining
the same physical adjoint flag. -/
theorem word_code_fourier (adjoint fourier : K → Bool)
    (C : AddSubgroup (K → AES.Word)) [Fintype C] :
    action (pairingFourier (WordFourierCore.wordPairing.product K))
        (action (coordinateKernel (fun k => variant (adjoint k) (fourier k)))
          (unitSubgroupIndicator C)) =
      action (coordinateKernel (fun k => variant (adjoint k) (!(fourier k))))
        (unitSubgroupIndicator ((WordFourierCore.wordPairing.product K).annihilator C)) := by
  simpa only [WordMarkedDual.variant_conjugate] using
    code_fourier WordFourierCore.wordPairing word_add_self
      (fun k => variant (adjoint k) (fourier k)) C

end WordCode

/-- The actual shortened source is identified with its marked image before
Fourier transport. The MDS injectivity threshold remains explicit. -/
theorem actual_source_fourier
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (T : Marked m → AES.Word → AES.Word → ℝ) :
    action (pairingFourier (WordFourierCore.wordPairing.product (Marked m)))
        (MixedCodeMoment.normalizedResponse T
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s)) =
      action (coordinateKernel (fun p => fourierConjugate WordFourierCore.wordPairing (T p)))
        (unitSubgroupIndicator
          ((WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s))) := by
  rw [normalized_source_eq_code m s hhigh]
  exact code_fourier WordFourierCore.wordPairing word_add_self T (markedCode m s)

/-- Actual word-variant response transport, preserving the input transpose
flags supplied by the physical vectorization. -/
theorem actual_variant_source_fourier
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (adjoint fourier : Marked m → Bool) :
    action (pairingFourier (WordFourierCore.wordPairing.product (Marked m)))
        (MixedCodeMoment.normalizedResponse
          (fun p => variant (adjoint p) (fourier p))
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s)) =
      action (coordinateKernel (fun p => variant (adjoint p) (!(fourier p))))
        (unitSubgroupIndicator
          ((WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s))) := by
  simpa only [WordMarkedDual.variant_conjugate] using
    actual_source_fourier m s hhigh (fun p => variant (adjoint p) (fourier p))

/-- The transported vector also has its exact normalized enumeration over
the actual annihilator, ready for a physical information-set factorization. -/
theorem actual_variant_source_fourier_normalized
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (adjoint fourier : Marked m → Bool) :
    action (pairingFourier (WordFourierCore.wordPairing.product (Marked m)))
        (MixedCodeMoment.normalizedResponse
          (fun p => variant (adjoint p) (fourier p))
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s)) =
      MixedCodeMoment.normalizedResponse
        (fun p => variant (adjoint p) (!(fourier p)))
        (fun c : (WordFourierCore.wordPairing.product (Marked m)).annihilator
          (markedCode m s) => c.val) := by
  rw [actual_variant_source_fourier m s hhigh adjoint fourier,
    MixedCodeMoment.subgroup_response]

end AESPaper.WordCodeFourier
