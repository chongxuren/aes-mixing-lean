import AESConcrete.WordColumnGram
import AESConcrete.ShortenedLineResponse

/-!
# Actual diffusion coordinates of one physical source byte

With the other three input coordinates fixed to zero, each output coordinate
is a zero-preserving bijection of the original byte source. This is derived
from the existing shortened MDS information-set theorem. The permutations
are identified pointwise with the actual forward/inverse AES diffusion.
No common scalar representation or Gram invariance is assumed.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
namespace AESConcrete.SingleByteCoordinates
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.WordColumnGram (Byte Word singleByteWord)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_size
  byteDiffusionHom byteDiffusionHom_zeroMDS byteDiffusionHom_apply output_coordinate_bijective)

def sourceZeroMask (k : Fin 4) : Fin 16 := maskComplement (singletonMask k)

theorem sourceZeroMask_bit : ∀ k i : Fin 4,
    maskBit (sourceZeroMask k) i = true ↔ i ≠ k := by decide

theorem sourceZeroMask_size (k : Fin 4) : maskSize (sourceZeroMask k) = 3 := by
  rw [sourceZeroMask, maskComplement_size, singletonMask_size]

/-- Insert the original source byte into the actual shortened input space. -/
def sourceGraphEquiv (inverse : Bool) (k : Fin 4) :
    Byte ≃ ShortenedGraph (byteDiffusionHom inverse) 0 (sourceZeroMask k) where
  toFun t := ⟨singleByteWord k t, by
    constructor
    · intro i hi
      rw [empty_mask_bit] at hi
      contradiction
    · intro i hi
      have hik := (sourceZeroMask_bit k i).mp hi
      simp [singleByteWord, hik]⟩
  invFun x := x.val k
  left_inv t := by simp [singleByteWord]
  right_inv x := by
    apply Subtype.ext
    change singleByteWord k (x.val k) = x.val
    funext i
    by_cases hi : i = k
    · subst i
      simp [singleByteWord]
    · have hxi := x.property.2 i ((sourceZeroMask_bit k i).mpr hi)
      simp [singleByteWord, hi, hxi]

theorem sourceGraphEquiv_apply (inverse : Bool) (k : Fin 4) (t : Byte) :
    (sourceGraphEquiv inverse k t).val = singleByteWord k t := rfl

def outputCoordinate (inverse : Bool) (k i : Fin 4) (t : Byte) : Byte :=
  byteDiffusionOrientation inverse (singleByteWord k t) i

/-- The original input source, rather than an unrelated line parameter,
is used in this concrete bijection. -/
theorem outputCoordinate_bijective (inverse : Bool) (k i : Fin 4) :
    Function.Bijective (outputCoordinate inverse k i) := by
  have hshort : maskSize 0 + maskSize (sourceZeroMask k) = 3 := by
    rw [sourceZeroMask_size, show maskSize (0 : Fin 16) = 0 by decide]
  have hi : maskBit (0 : Fin 16) i ≠ true := by
    rw [empty_mask_bit]
    decide
  have hb := output_coordinate_bijective
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    0 (sourceZeroMask k) hshort i hi
  have h := hb.comp (sourceGraphEquiv inverse k).bijective
  change Function.Bijective
    (fun t : Byte => byteDiffusionHom inverse (singleByteWord k t) i) at h
  change Function.Bijective
    (fun t : Byte => byteDiffusionOrientation inverse (singleByteWord k t) i)
  simpa only [byteDiffusionHom_apply] using h

theorem outputCoordinate_zero (inverse : Bool) (k i : Fin 4) :
    outputCoordinate inverse k i 0 = 0 := by
  have hz : singleByteWord k (0 : Byte) = (0 : Word) := by
    funext j
    simp [singleByteWord]
  unfold outputCoordinate
  rw [hz, byteDiffusionOrientation_zero]
  rfl

/-- The actual zero-preserving output coordinate permutation. -/
def coordinatePerm (inverse : Bool) (k i : Fin 4) : Equiv.Perm Byte :=
  Equiv.ofBijective (outputCoordinate inverse k i) (outputCoordinate_bijective inverse k i)

theorem coordinatePerm_apply (inverse : Bool) (k i : Fin 4) (t : Byte) :
    coordinatePerm inverse k i t =
      byteDiffusionOrientation inverse (singleByteWord k t) i := rfl

theorem coordinatePerm_zero (inverse : Bool) (k i : Fin 4) :
    coordinatePerm inverse k i 0 = 0 := outputCoordinate_zero inverse k i

theorem coordinatePerm_symm_zero (inverse : Bool) (k i : Fin 4) :
    (coordinatePerm inverse k i).symm 0 = 0 := by
  apply (coordinatePerm inverse k i).injective
  rw [Equiv.apply_symm_apply, coordinatePerm_zero]

theorem coordinatePerm_ne_zero (inverse : Bool) (k i : Fin 4) (t : Byte) (ht : t ≠ 0) :
    coordinatePerm inverse k i t ≠ 0 := by
  intro h
  exact ht ((coordinatePerm inverse k i).injective (h.trans (coordinatePerm_zero inverse k i).symm))

end AESConcrete.SingleByteCoordinates
