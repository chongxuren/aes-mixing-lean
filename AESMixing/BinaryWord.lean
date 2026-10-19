import AESMixing.AESByte
import AESMixing.Markov
import Mathlib.Data.Fintype.Pi

/-! A distinct type prevents modular byte addition from being confused with
the XOR addition used by AES and the difference-channel model. -/
namespace AESMixing

structure BinaryWord (n : ℕ) where
  bits : BitVec n
  deriving DecidableEq

namespace BinaryWord

theorem ext {n : ℕ} {x y : BinaryWord n} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

def equivFin (n : ℕ) : BinaryWord n ≃ Fin (2 ^ n) where
  toFun x := x.bits.toFin
  invFun x := ⟨BitVec.ofFin x⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl

instance {n : ℕ} : Fintype (BinaryWord n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (equivFin n).symm

theorem card (n : ℕ) : Fintype.card (BinaryWord n) = 2 ^ n := by
  rw [Fintype.card_congr (equivFin n), Fintype.card_fin]

instance {n : ℕ} : Zero (BinaryWord n) := ⟨⟨0⟩⟩
instance {n : ℕ} : Add (BinaryWord n) := ⟨fun x y => ⟨x.bits ^^^ y.bits⟩⟩
instance {n : ℕ} : Neg (BinaryWord n) := ⟨id⟩

instance {n : ℕ} : AddCommGroup (BinaryWord n) where
  add_assoc x y z := ext (BitVec.xor_assoc x.bits y.bits z.bits)
  zero_add _ := ext BitVec.zero_xor
  add_zero _ := ext BitVec.xor_zero
  add_comm x y := ext (BitVec.xor_comm x.bits y.bits)
  neg_add_cancel _ := ext BitVec.xor_self
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem add_bits {n : ℕ} (x y : BinaryWord n) :
    (x + y).bits = x.bits ^^^ y.bits := rfl

theorem sub_eq_add {n : ℕ} (x y : BinaryWord n) : x - y = x + y := rfl

def sboxPerm : Equiv.Perm (BinaryWord 8) where
  toFun x := ⟨AES.sbox x.bits⟩
  invFun x := ⟨AES.invSbox x.bits⟩
  left_inv x := ext (AES.sboxPerm.left_inv x.bits)
  right_inv x := ext (AES.sboxPerm.right_inv x.bits)

end BinaryWord

/-- The concrete AES byte channel, with XOR differences. -/
noncomputable def aesByteChannel : BinaryWord 8 → BinaryWord 8 → ℝ :=
  differenceChannel BinaryWord.sboxPerm

theorem aesByteChannel_column (a : BinaryWord 8) :
    (∑ b, aesByteChannel b a) = 1 := differenceChannel_column _ a

theorem aesByteChannel_row (b : BinaryWord 8) :
    (∑ a, aesByteChannel b a) = 1 := differenceChannel_row _ b

theorem aesByteChannel_stationary :
    action aesByteChannel (uniformExcept (0 : BinaryWord 8)) = uniformExcept 0 :=
  differenceChannel_stationary _

end AESMixing
