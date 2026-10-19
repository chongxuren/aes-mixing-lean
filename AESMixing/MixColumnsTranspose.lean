import AESMixing.GramCases

/-! The transpose cases needed by adjoints and Fourier conjugation are
coordinate reversals of forward/inverse AES MixColumns. The subsequent
operator proof must also use invariance of degree spaces under reordering. -/
namespace AESMixing
open scoped BigOperators

def byteReverse : Equiv.Perm (Fin 4) where
  toFun i := ![0,3,2,1] i
  invFun i := ![0,3,2,1] i
  left_inv := by decide
  right_inv := by decide

theorem byteReverse_self : ∀ i, byteReverse (byteReverse i) = i := by decide

theorem gramMixing_reverse : ∀ inverse : Bool, ∀ i j : Fin 4,
    gramMixing inverse (byteReverse i) (byteReverse j) = gramMixing inverse j i := by decide

theorem gramMixing_transpose_action (inverse : Bool) (x : Fin 4 → BinaryWord 8) :
    fieldMatrix (fun i j => gramMixing inverse j i) x =
      fun i => fieldMatrix (gramMixing inverse) (fun j => x (byteReverse j)) (byteReverse i) := by
  funext i
  have h := Equiv.sum_comp byteReverse
    (fun j => gramMixing inverse (byteReverse i) j * x (byteReverse j))
  simpa only [fieldMatrix, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    gramMixing_reverse, byteReverse_self] using h

end AESMixing
