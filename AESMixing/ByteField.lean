import AESMixing.ByteRing
import Mathlib.Algebra.Field.Basic

/-! A field structure on the actual AES byte representation. The inverse
operation is the concrete exponent-254 routine already used by the S-box. -/
namespace AESMixing.BinaryWord

instance : One (BinaryWord 8) := ⟨⟨1⟩⟩
instance : Mul (BinaryWord 8) := ⟨fun x y => ⟨AES.mul x.bits y.bits⟩⟩

instance : CommRing (BinaryWord 8) where
  mul_assoc x y z := ext (AES.mul_assoc x.bits y.bits z.bits)
  one_mul x := ext (AES.one_mul x.bits)
  mul_one x := ext (AES.mul_one x.bits)
  left_distrib x y z := ext (AES.mul_xor_right x.bits y.bits z.bits)
  right_distrib x y z := ext (AES.mul_xor x.bits y.bits z.bits)
  zero_mul x := ext (AES.mul_zero_left x.bits)
  mul_zero x := ext (AES.mul_zero_right x.bits)
  mul_comm x y := ext (AES.mul_comm x.bits y.bits)

instance : Inv (BinaryWord 8) := ⟨fun x => ⟨AES.inv x.bits⟩⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem byte_mul_inv_fin (x : Fin 256) : x ≠ 0 →
    AES.mul (BitVec.ofFin x) (AES.inv (BitVec.ofFin x)) = 1 := by
  fin_cases x <;> decide

instance : Nontrivial (BinaryWord 8) := ⟨⟨0, 1, by decide⟩⟩

set_option maxRecDepth 16384 in
instance : Field (BinaryWord 8) where
  mul_inv_cancel x hx := by
    apply ext
    exact byte_mul_inv_fin x.bits.toFin (by
      intro h
      apply hx
      apply ext
      exact congrArg BitVec.ofFin h)
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

theorem mul_bits (x y : BinaryWord 8) : (x * y).bits = AES.mul x.bits y.bits := rfl
theorem inv_bits (x : BinaryWord 8) : (x⁻¹).bits = AES.inv x.bits := rfl

theorem neg_eq_self (x : BinaryWord 8) : -x = x := rfl
theorem add_self (x : BinaryWord 8) : x + x = 0 := ext BitVec.xor_self

end AESMixing.BinaryWord
