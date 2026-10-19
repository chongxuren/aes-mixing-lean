import AESMixing.BinaryWord
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Hom.Basic

/-! Additive structure of concrete AES polynomial multiplication. This lets
finite basis certificates establish diffusion identities on all words. -/
namespace AESMixing.AES
open scoped BigOperators

theorem xtime_xor (x y : Byte) : xtime (x ^^^ y) = xtime x ^^^ xtime y := by
  have hcomm (a b c : Byte) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by ac_rfl
  simp only [xtime, BitVec.shiftLeft_xor_distrib, BitVec.getMsbD_xor]
  cases hx : x.getMsbD 0 <;> cases hy : y.getMsbD 0 <;>
    simp [BitVec.xor_assoc, BitVec.xor_comm, hcomm]

theorem mulAux_xor (n : ℕ) (a1 a2 b c1 c2 : Byte) :
    mulAux n (a1 ^^^ a2) b (c1 ^^^ c2) =
      mulAux n a1 b c1 ^^^ mulAux n a2 b c2 := by
  induction n generalizing a1 a2 b c1 c2 with
  | zero => rfl
  | succ n ih =>
    have hc : (c1 ^^^ c2) ^^^ (a1 ^^^ a2) = (c1 ^^^ a1) ^^^ (c2 ^^^ a2) := by
      ac_rfl
    cases hb : b.getLsbD 0 <;> simp only [mulAux, hb, Bool.false_eq_true, if_false,
      if_true, xtime_xor, hc, ih]

theorem mul_xor (x y c : Byte) : mul (x ^^^ y) c = mul x c ^^^ mul y c := by
  change mulAux 8 (x ^^^ y) c (0#8) = mulAux 8 x c (0#8) ^^^ mulAux 8 y c (0#8)
  have h := mulAux_xor 8 x y c (0#8) (0#8)
  simpa only [BitVec.xor_self] using h

theorem mul_zero_left (c : Byte) : mul 0 c = 0 := by
  change mul (0#8) c = (0#8)
  have h := mul_xor (0#8) (0#8) c
  simpa only [BitVec.xor_self] using h

def scale (c : Byte) : BinaryWord 8 →+ BinaryWord 8 where
  toFun x := ⟨mul x.bits c⟩
  map_zero' := BinaryWord.ext (mul_zero_left c)
  map_add' x y := BinaryWord.ext (mul_xor x.bits y.bits c)

def byteBasis (i : Fin 8) : BinaryWord 8 := ⟨BitVec.ofNat 8 (2 ^ i.val)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem byte_basis_decomposition_fin (x : Fin 256) :
    (⟨BitVec.ofFin x⟩ : BinaryWord 8) =
      ∑ i : Fin 8, if (BitVec.ofFin x : Byte).getLsbD i.val then byteBasis i else 0 := by
  fin_cases x <;> decide

theorem byte_basis_decomposition (x : BinaryWord 8) :
    x = ∑ i : Fin 8, if x.bits.getLsbD i.val then byteBasis i else 0 :=
  byte_basis_decomposition_fin x.bits.toFin

theorem byte_addHom_ext {A : Type*} [AddCommMonoid A]
    (f g : BinaryWord 8 →+ A) (h : ∀ i, f (byteBasis i) = g (byteBasis i)) : f = g := by
  apply DFunLike.ext
  intro x
  rw [byte_basis_decomposition x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [h]

end AESMixing.AES
