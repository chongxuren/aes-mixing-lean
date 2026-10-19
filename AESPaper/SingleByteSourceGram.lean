import AESConcrete.SingleByteCoordinates
import AESConcrete.ByteGramFourier

/-!
# The common residual Gram of one actual forward source byte
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace AESPaper.SingleByteSourceGram
open AESMixing
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.SingleByteCoordinates (coordinatePerm)

/-- The actual forward coordinate map is multiplication by its actual
MixColumns field coefficient, on the original source byte. -/
theorem forward_coordinate_scalar (k i : Fin 4) (x : Byte) :
    coordinatePerm false k i x = gramMixing false i k * x := by
  rw [AESConcrete.SingleByteCoordinates.coordinatePerm_apply, byteDiffusionOrientation_apply]
  simp [fieldMatrix, AESConcrete.WordColumnGram.singleByteWord, mul_ite]

-- Only the sixteen concrete MixColumns coefficients are checked here.
theorem forward_coefficient_ne_zero : ∀ i k : Fin 4, gramMixing false i k ≠ 0 := by decide

/-- All four ordinary residual response Grams coincide on the original
source labels. No product assumption or Gram estimate is used. -/
theorem forward_residual_gram (k i : Fin 4) (x z : Byte) :
    residualGram aesByteChannel (coordinatePerm false k i x) (coordinatePerm false k i z) =
      residualGram aesByteChannel x z := by
  rw [AESConcrete.ByteGramCore.aes_gram, AESConcrete.ByteGramCore.aes_gram,
    forward_coordinate_scalar, forward_coordinate_scalar]
  exact AESConcrete.ByteGramFourier.inversion_gram_scale
    (gramMixing false i k) (forward_coefficient_ne_zero i k) x z

end AESPaper.SingleByteSourceGram
