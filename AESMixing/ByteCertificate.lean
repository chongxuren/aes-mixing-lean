import AESMixing.AESByte
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! An acceleration table, generated on TS1000 and checked against the
concrete exponent-254 inverse at every byte. No table entry is assumed correct.
Generator log SHA-256: 11d8765534d5e581058591f219b915a9758dbe9828ee3f3b57cc25a93feed982
-/
namespace AESMixing.AES
open scoped BigOperators

def inverseTable : Array Byte := #[0,1,141,246,203,82,123,209,232,79,41,192,176,225,229,199,116,180,170,75,153,43,96,95,88,63,253,204,255,64,238,178,58,110,90,241,85,77,168,201,193,10,152,21,48,68,162,194,44,69,146,108,243,57,102,66,242,53,32,111,119,187,89,25,29,254,55,103,45,49,245,105,167,100,171,19,84,37,233,9,237,92,5,202,76,36,135,191,24,62,34,240,81,236,97,23,22,94,175,211,73,166,54,67,244,71,145,223,51,147,33,59,121,183,151,133,16,181,186,60,182,112,208,6,161,250,129,130,131,126,127,128,150,115,190,86,155,158,149,217,247,2,185,164,222,106,50,109,216,138,132,114,42,20,159,136,249,220,137,154,251,124,46,195,143,184,101,72,38,200,18,74,206,231,210,98,12,224,31,239,17,117,120,113,165,142,118,61,189,188,134,87,11,40,47,163,218,212,228,15,169,39,83,4,27,252,172,230,122,7,174,99,197,219,226,234,148,139,196,213,157,248,144,107,177,13,214,235,198,14,207,173,8,78,215,227,93,80,30,179,91,35,56,52,104,70,3,140,221,156,125,160,205,26,65,28]
def invLookup (x : Byte) : Byte := inverseTable[x.toNat]!

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem invLookup_correct_fin (x : Fin 256) :
    invLookup (BitVec.ofFin x) = inv (BitVec.ofFin x) := by
  fin_cases x <;> decide

theorem invLookup_correct (x : Byte) : invLookup x = inv x :=
  invLookup_correct_fin x.toFin

def traceBit (x : Byte) : Bool := xor (x.getLsbD 5) (x.getLsbD 7)

def inversionRowOneCount (b : Byte) : ℕ :=
  ∑ x : Fin 256,
    if invLookup (BitVec.ofFin x ^^^ 1) ^^^ invLookup (BitVec.ofFin x) = b then 1 else 0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 80000000 in
theorem inversion_row_one_certificate (b : Fin 256) : b ≠ 0 →
    inversionRowOneCount (BitVec.ofFin b) =
      (if traceBit (invLookup (BitVec.ofFin b)) then 0 else 2) +
        (if b = 1 then 2 else 0) := by
  fin_cases b <;> decide

end AESMixing.AES
