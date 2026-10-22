import AES8.Model.Byte.PaperAESBase

namespace AES8.PaperAESAlgebraic
open Polynomial AESMixing
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 8192

@[simp] private theorem bits_zero : (0 : Byte).bits = (0#8) := rfl

@[simp] private theorem bit_zero (i : Nat) :
    (0 : Byte).bits.getLsbD i = false := by
  change (0#8).getLsbD i = false
  simp

private theorem bit_add (x y : Byte) (i : Fin 8) :
    (x+y).bits.getLsbD i.val = (x.bits.getLsbD i.val ^^ y.bits.getLsbD i.val) := by
  rw [BinaryWord.add_bits, BitVec.getLsbD_xor]

private theorem bit_term (c : ZMod 2) (i j : Fin 8) :
    (if c = 0 then (0 : Byte) else AES.byteBasis j).bits.getLsbD i.val =
      if i = j then (if c = 0 then false else true) else false := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [hc, if_false]
    fin_cases i <;> fin_cases j <;> decide

/-- Each output bit is precisely its matching binary coefficient. -/
theorem byteEval_bit (v : Fin 8 → ZMod 2) (i : Fin 8) :
    (byteEval v).bits.getLsbD i.val = if v i = 0 then false else true := by
  simp only [byteEval, Fin.sum_univ_succ, bit_add, bit_term]
  fin_cases i <;> simp

theorem byteEval_zero (v : Fin 8 → ZMod 2) : byteEval v = 0 → v = 0 := by
  intro h
  funext i
  have he := congrArg (fun x : Byte => x.bits.getLsbD i.val) h
  rw [byteEval_bit] at he
  by_contra hi
  change v i ≠ 0 at hi
  simp [hi] at he


end AES8.PaperAESAlgebraic
