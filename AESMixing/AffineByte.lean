import AESMixing.ByteLinear
import Mathlib.Data.Fintype.EquivFin

/-! The concrete affine output map of the AES S-box as an additive equivalence. -/
namespace AESMixing.AES

theorem rotateLeft_xor (x y : Byte) (r : ℕ) :
    (x ^^^ y).rotateLeft r = x.rotateLeft r ^^^ y.rotateLeft r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
  by_cases h : i < r % 8 <;> simp [h]

def affineLinearByte (x : Byte) : Byte :=
  x ^^^ x.rotateLeft 1 ^^^ x.rotateLeft 2 ^^^ x.rotateLeft 3 ^^^ x.rotateLeft 4

def invAffineLinearByte (x : Byte) : Byte :=
  x.rotateLeft 1 ^^^ x.rotateLeft 3 ^^^ x.rotateLeft 6

theorem affineLinear_xor (x y : Byte) :
    affineLinearByte (x ^^^ y) = affineLinearByte x ^^^ affineLinearByte y := by
  simp only [affineLinearByte, rotateLeft_xor]
  ac_rfl

theorem invAffineLinear_xor (x y : Byte) :
    invAffineLinearByte (x ^^^ y) = invAffineLinearByte x ^^^ invAffineLinearByte y := by
  simp only [invAffineLinearByte, rotateLeft_xor]
  ac_rfl

def affineLinear : BinaryWord 8 →+ BinaryWord 8 where
  toFun x := ⟨affineLinearByte x.bits⟩
  map_zero' := by decide
  map_add' x y := BinaryWord.ext (affineLinear_xor x.bits y.bits)

def invAffineLinear : BinaryWord 8 →+ BinaryWord 8 where
  toFun x := ⟨invAffineLinearByte x.bits⟩
  map_zero' := by decide
  map_add' x y := BinaryWord.ext (invAffineLinear_xor x.bits y.bits)

theorem affineLinear_left_inverse : Function.LeftInverse invAffineLinear affineLinear := by
  have he : invAffineLinear.comp affineLinear = AddMonoidHom.id (BinaryWord 8) := by
    apply byte_addHom_ext
    intro i
    fin_cases i <;> decide
  intro x
  exact DFunLike.congr_fun he x

noncomputable def affineLinearEquiv : BinaryWord 8 ≃+ BinaryWord 8 :=
  AddEquiv.ofBijective affineLinear
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨affineLinear_left_inverse.injective, rfl⟩)

theorem sbox_affine (x : BinaryWord 8) :
    BinaryWord.sboxPerm x = affineLinearEquiv (⟨inv x.bits⟩ : BinaryWord 8) + ⟨0x63⟩ := rfl

end AESMixing.AES
