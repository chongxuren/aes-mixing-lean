import AES8.Model.ByteTrace

/-! Paper-facing trace names reuse the existing concrete trace certificate.
The finite polynomial evaluation has one owner in `AES8.Model.ByteTrace`. -/
noncomputable section
namespace AES8.PaperByteTrace
open AESMixing
set_option autoImplicit false

abbrev Byte := BinaryWord 8
abbrev absoluteTrace : Byte → Byte := ByteTrace.absoluteTrace

theorem absoluteTrace_eq (x : Byte) :
    absoluteTrace x = if AES.traceBit x.bits then 1 else 0 :=
  ByteTrace.absoluteTrace_eq_traceBit x

theorem absoluteTrace_zero_iff (x : Byte) :
    absoluteTrace x = 0 ↔ AES.traceBit x.bits = false := by
  rw [absoluteTrace_eq]
  cases h : AES.traceBit x.bits <;> simp

def traceCharacter (x : Byte) : ℝ := if absoluteTrace x = 0 then 1 else -1

theorem traceCharacter_eq (x : Byte) : traceCharacter x = byteCharacter x :=
  (ByteTrace.byteCharacter_eq_trace x).symm

end AES8.PaperByteTrace
