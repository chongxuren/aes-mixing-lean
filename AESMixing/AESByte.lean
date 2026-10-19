import AESMixing.Scalar
import Mathlib.Tactic.FinCases

/-! Concrete FIPS-197 byte operations. Addition here is bitwise XOR, not
the built-in modular addition on BitVec. No abstract field is substituted
for the AES polynomial representation. -/
namespace AESMixing.AES

set_option maxRecDepth 8192

abbrev Byte := BitVec 8

def xtime (x : Byte) : Byte :=
  (x <<< 1) ^^^ (if x.getMsbD 0 then 0x1b else 0)

def mulAux : Nat → Byte → Byte → Byte → Byte
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => mulAux n (xtime a) (b >>> 1)
      (if b.getLsbD 0 then acc ^^^ a else acc)

/-- Polynomial multiplication modulo X^8 + X^4 + X^3 + X + 1. -/
def mul (a b : Byte) : Byte := mulAux 8 a b 0

/-- The exponent 254 is 2+4+8+16+32+64+128; zero maps to zero. -/
def inv (x : Byte) : Byte :=
  let x2 := mul x x
  let x4 := mul x2 x2
  let x8 := mul x4 x4
  let x16 := mul x8 x8
  let x32 := mul x16 x16
  let x64 := mul x32 x32
  let x128 := mul x64 x64
  mul (mul (mul (mul (mul (mul x2 x4) x8) x16) x32) x64) x128

def affine (x : Byte) : Byte :=
  x ^^^ x.rotateLeft 1 ^^^ x.rotateLeft 2 ^^^ x.rotateLeft 3 ^^^
    x.rotateLeft 4 ^^^ 0x63

def invAffine (x : Byte) : Byte :=
  x.rotateLeft 1 ^^^ x.rotateLeft 3 ^^^ x.rotateLeft 6 ^^^ 0x05

def sbox (x : Byte) : Byte := affine (inv x)
def invSbox (x : Byte) : Byte := inv (invAffine x)

theorem xtime_fips_example : xtime 0x57 = 0xae := by decide
theorem mul_fips_example : mul 0x57 0x13 = 0xfe := by decide
theorem sbox_zero : sbox 0 = 0x63 := by decide
theorem sbox_fips_example : sbox 0x53 = 0xed := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem inv_involutive_fin (x : Fin 256) :
    inv (inv (BitVec.ofFin x)) = BitVec.ofFin x := by
  fin_cases x <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem affine_left_inverse_fin (x : Fin 256) :
    invAffine (affine (BitVec.ofFin x)) = BitVec.ofFin x := by
  fin_cases x <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem affine_right_inverse_fin (x : Fin 256) :
    affine (invAffine (BitVec.ofFin x)) = BitVec.ofFin x := by
  fin_cases x <;> decide

theorem inv_involutive (x : Byte) : inv (inv x) = x :=
  inv_involutive_fin x.toFin

theorem affine_left_inverse (x : Byte) : invAffine (affine x) = x :=
  affine_left_inverse_fin x.toFin

theorem affine_right_inverse (x : Byte) : affine (invAffine x) = x :=
  affine_right_inverse_fin x.toFin

def sboxPerm : Equiv.Perm Byte where
  toFun := sbox
  invFun := invSbox
  left_inv x := by
    simp only [invSbox, sbox, affine_left_inverse, inv_involutive]
  right_inv x := by
    simp only [invSbox, sbox, inv_involutive, affine_right_inverse]

end AESMixing.AES
