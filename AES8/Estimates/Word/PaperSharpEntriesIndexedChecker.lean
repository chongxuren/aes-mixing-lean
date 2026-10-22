import AES8.Estimates.Word.PaperSharpEntriesFWHT

/-! Exact index-form evaluation interface. Mathematical Byte quantifiers remain
in the specification; certificate loops can use Fin256 without repeated
transport through its Fintype instance. This supplies no cap certificate. -/

open scoped BigOperators
namespace AES8.PaperSharpEntriesIndexedChecker
open AESMixing
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesFWHT (Index byteOf)
set_option autoImplicit false

def indexedSum (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta gamma : Byte) (r : ℕ) : ℕ :=
  ∑ i : Index, profile (byteOf i)^r *
    profile (alpha * B (beta * byteOf i) + gamma)^(5-r)

theorem mixedSum_eq_indexed (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta gamma : Byte) (r : ℕ) :
    mixedSum profile B alpha beta gamma r = indexedSum profile B alpha beta gamma r := by
  exact (Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun u : Byte => profile u^r * profile (alpha * B (beta*u)+gamma)^(5-r))).symm

def checkMap (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ) : Bool :=
  decide (∀ gamma : Index,
    indexedSum profile B (nonzeroByte alpha) (nonzeroByte beta) (byteOf gamma) r ≤ cap)

theorem checkMap_sound (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ)
    (hc : checkMap profile B alpha beta r cap = true) (gamma : Byte) :
    mixedSum profile B (nonzeroByte alpha) (nonzeroByte beta) gamma r ≤ cap := by
  rw [mixedSum_eq_indexed]
  exact (of_decide_eq_true hc) gamma.bits.toFin

end AES8.PaperSharpEntriesIndexedChecker
