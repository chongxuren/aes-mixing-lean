import AESMixing.ByteLinear
import Mathlib.Algebra.Ring.Defs

/-! The concrete polynomial multiplication is bilinear over XOR. Its ring
identities are checked on binary basis vectors and then extended by additivity. -/
namespace AESMixing.AES
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem mulAux_xor_right (n : ℕ) (a b1 b2 c1 c2 : Byte) :
    mulAux n a (b1 ^^^ b2) (c1 ^^^ c2) =
      mulAux n a b1 c1 ^^^ mulAux n a b2 c2 := by
  induction n generalizing a b1 b2 c1 c2 with
  | zero => rfl
  | succ n ih =>
    have hc : (c1 ^^^ a) ^^^ (c2 ^^^ a) = c1 ^^^ c2 := by
      have he : (c1 ^^^ a) ^^^ (c2 ^^^ a) = (c1 ^^^ c2) ^^^ (a ^^^ a) := by ac_rfl
      rw [he, BitVec.xor_self, BitVec.xor_zero]
    have hr : (c1 ^^^ c2) ^^^ a = c1 ^^^ (c2 ^^^ a) := by ac_rfl
    have hl : (c1 ^^^ c2) ^^^ a = (c1 ^^^ a) ^^^ c2 := by ac_rfl
    cases h1 : b1.getLsbD 0 <;> cases h2 : b2.getLsbD 0 <;>
      simp only [mulAux, BitVec.getLsbD_xor, h1, h2, Bool.xor_false,
        Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_false, if_true, BitVec.ushiftRight_xor_distrib]
    · exact ih _ _ _ _ _
    · rw [hr]; exact ih _ _ _ _ _
    · rw [hl]; exact ih _ _ _ _ _
    · rw [← hc]; exact ih _ _ _ _ _

theorem mul_xor_right (c x y : Byte) : mul c (x ^^^ y) = mul c x ^^^ mul c y := by
  change mulAux 8 c (x ^^^ y) (0#8) = mulAux 8 c x (0#8) ^^^ mulAux 8 c y (0#8)
  have h := mulAux_xor_right 8 c x y (0#8) (0#8)
  simpa only [BitVec.xor_self] using h

theorem mul_zero_right (c : Byte) : mul c 0 = 0 := by
  change mul c (0#8) = (0#8)
  have h := mul_xor_right c (0#8) (0#8)
  simpa only [BitVec.xor_self] using h

def leftScale (c : Byte) : BinaryWord 8 →+ BinaryWord 8 where
  toFun x := ⟨mul c x.bits⟩
  map_zero' := BinaryWord.ext (mul_zero_right c)
  map_add' x y := BinaryWord.ext (mul_xor_right c x.bits y.bits)

theorem mul_comm_basis (i j : Fin 8) :
    mul (byteBasis i).bits (byteBasis j).bits =
      mul (byteBasis j).bits (byteBasis i).bits := by
  fin_cases i <;> fin_cases j <;> decide

theorem mul_comm (x y : Byte) : mul x y = mul y x := by
  have hi (i : Fin 8) : leftScale (byteBasis i).bits = scale (byteBasis i).bits := by
    apply byte_addHom_ext
    intro j
    exact BinaryWord.ext (mul_comm_basis i j)
  have he : scale y = leftScale y := by
    apply byte_addHom_ext
    intro i
    simpa only [leftScale, scale, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
      DFunLike.congr_fun (hi i) (⟨y⟩ : BinaryWord 8)
  exact congrArg (fun w : BinaryWord 8 => w.bits)
    (DFunLike.congr_fun he (⟨x⟩ : BinaryWord 8))

set_option maxRecDepth 8192 in
theorem mul_assoc_basis (i j k : Fin 8) :
    mul (mul (byteBasis i).bits (byteBasis j).bits) (byteBasis k).bits =
      mul (byteBasis i).bits (mul (byteBasis j).bits (byteBasis k).bits) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem mul_assoc (x y z : Byte) : mul (mul x y) z = mul x (mul y z) := by
  have hi (i j : Fin 8) :
      leftScale (mul (byteBasis i).bits (byteBasis j).bits) =
        (leftScale (byteBasis i).bits).comp (leftScale (byteBasis j).bits) := by
    apply byte_addHom_ext
    intro k
    exact BinaryWord.ext (mul_assoc_basis i j k)
  have hj (i : Fin 8) :
      (scale z).comp (leftScale (byteBasis i).bits) =
        (leftScale (byteBasis i).bits).comp (scale z) := by
    apply byte_addHom_ext
    intro j
    simpa only [AddMonoidHom.comp_apply, leftScale, scale,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
      DFunLike.congr_fun (hi i j) (⟨z⟩ : BinaryWord 8)
  have he : (scale z).comp (scale y) = scale (mul y z) := by
    apply byte_addHom_ext
    intro i
    simpa only [AddMonoidHom.comp_apply, leftScale, scale,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
      DFunLike.congr_fun (hj i) (⟨y⟩ : BinaryWord 8)
  exact congrArg (fun w : BinaryWord 8 => w.bits)
    (DFunLike.congr_fun he (⟨x⟩ : BinaryWord 8))

theorem mul_one (x : Byte) : mul x 1 = x := by
  have he : scale 1 = AddMonoidHom.id (BinaryWord 8) := by
    apply byte_addHom_ext
    intro i
    fin_cases i <;> decide
  exact congrArg (fun w : BinaryWord 8 => w.bits)
    (DFunLike.congr_fun he (⟨x⟩ : BinaryWord 8))

theorem one_mul (x : Byte) : mul 1 x = x := by rw [mul_comm, mul_one]

end AESMixing.AES
