import AESMixing.ByteWalshDefinition

/-! Candidate Walsh table generated on TS1000; every entry is checked below
against the concrete polynomial-byte sum by ordinary kernel evaluation.
Generator log SHA-256: e276d967af4bd5ecdb7ae4aec404497e6c95a43a498d4ba2e27d0655df481d14
-/
namespace AESMixing.AES
open scoped BigOperators

def inversionWalshTable : Array ℤ := #[0,32,-16,-16,-16,-16,0,16,16,0,16,0,24,8,24,-8,-16,-16,8,8,0,16,-8,24,8,-24,-16,-16,0,16,8,8,12,-28,-4,-12,4,-4,-12,-4,-4,-12,-4,-12,-4,-12,28,4,20,12,-4,20,28,4,4,28,28,4,20,-4,-4,-12,-12,-4,16,0,-8,-8,16,0,-24,24,8,-24,16,0,-16,-16,8,8,24,8,24,-8,24,-8,-24,8,-24,24,-24,8,32,32,-16,-16,4,-4,28,4,-4,-12,4,28,-4,-12,20,-4,12,-28,-12,-20,20,12,20,-4,-4,4,12,20,-12,-4,20,12,4,-4,-12,-20,12,-28,-4,20,-12,-20,-12,-4,-12,-20,-12,-20,4,-4,-12,-4,-28,12,-20,-12,12,-28,-28,12,20,12,12,-28,-12,-4,-4,20,24,-8,-8,-8,-24,8,24,-24,16,0,0,16,24,-24,-8,-8,24,8,0,16,24,-8,16,0,-24,24,0,16,-16,-16,24,-24,12,20,4,28,-28,12,-4,4,12,20,4,-4,-4,4,-12,-4,-4,-12,28,4,20,-4,-12,-4,20,-4,-12,-20,20,12,-12,-20,32,32,24,-24,-16,-16,-24,8,16,0,-24,8,8,24,0,16,-24,24,-8,-8,-24,8,24,-8,0,16,-16,-16,-8,24,8,8]
def inversionWalshLookup (v : Byte) : ℤ := inversionWalshTable[v.toNat]!

set_option maxRecDepth 65536 in
set_option maxHeartbeats 80000000 in
theorem inversionWalshLookup_correct_fin (v : Fin 256) :
    inversionWalshLookup (BitVec.ofFin v) = inversionWalshOne (BitVec.ofFin v) := by
  fin_cases v <;> decide

theorem inversionWalshLookup_correct (v : Byte) :
    inversionWalshLookup v = inversionWalshOne v := inversionWalshLookup_correct_fin v.toFin

set_option maxRecDepth 65536 in
theorem inversion_walsh_bound_certificate (v : Fin 256) :
    inversionWalshLookup (BitVec.ofFin v)^2 ≤ 1024 := by fin_cases v <;> decide

set_option maxRecDepth 65536 in
theorem inversion_walsh_second_certificate :
    (∑ v : Fin 256, inversionWalshLookup (BitVec.ofFin v)^2) = 65536 := by decide

set_option maxRecDepth 65536 in
theorem inversion_walsh_fourth_certificate :
    (∑ v : Fin 256, inversionWalshLookup (BitVec.ofFin v)^4) = 65 * 2^19 := by decide

end AESMixing.AES
