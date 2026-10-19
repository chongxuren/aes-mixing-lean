import AESMixing.ByteCertificate

/-! Exact integer Walsh coefficients for inversion with first mask one.
Kernel verification of the proposed table is owned by ByteWalshCertificate. -/
namespace AESMixing.AES
open scoped BigOperators

def inversionWalshOne (v : Byte) : ℤ :=
  ∑ x : Fin 256, if traceBit (BitVec.ofFin x ^^^ mul v (invLookup (BitVec.ofFin x)))
    then -1 else 1

end AESMixing.AES
