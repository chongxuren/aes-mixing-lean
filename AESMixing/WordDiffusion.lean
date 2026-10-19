import AESMixing.Diffusion

/-! The word-level MDS property of L = ShiftRows o MixColumns o ShiftRows.
Reindexing by diagonals reduces each constraint to the checked byte MDS map. -/
namespace AESMixing.AES
open scoped BigOperators

def projectColumns (mask : Fin 16) (x : State) : State :=
  fun row col => if maskBit mask col then x row col else 0

def wordDiffusion (x : State) : State := shiftRows (mixColumns (shiftRows x))

def inputDiagonalMask (mask : Fin 16) (d : Fin 4) : Fin 16 :=
  ⟨(∑ i : Fin 4, if maskBit mask (d + i) then 2 ^ i.val else 0) % 16,
    Nat.mod_lt _ (by decide)⟩

def outputDiagonalMask (mask : Fin 16) (d : Fin 4) : Fin 16 :=
  ⟨(∑ i : Fin 4, if maskBit mask (d - i) then 2 ^ i.val else 0) % 16,
    Nat.mod_lt _ (by decide)⟩

theorem inputDiagonalMask_bit (mask : Fin 16) (d i : Fin 4) :
    maskBit (inputDiagonalMask mask d) i = maskBit mask (d + i) := by
  fin_cases mask <;> fin_cases d <;> fin_cases i <;> decide

theorem outputDiagonalMask_bit (mask : Fin 16) (d i : Fin 4) :
    maskBit (outputDiagonalMask mask d) i = maskBit mask (d - i) := by
  fin_cases mask <;> fin_cases d <;> fin_cases i <;> decide

theorem inputDiagonalMask_size (mask : Fin 16) (d : Fin 4) :
    maskSize (inputDiagonalMask mask d) = maskSize mask := by
  fin_cases mask <;> fin_cases d <;> decide

theorem outputDiagonalMask_size (mask : Fin 16) (d : Fin 4) :
    maskSize (outputDiagonalMask mask d) = maskSize mask := by
  fin_cases mask <;> fin_cases d <;> decide

theorem fin4_sub_add (d row : Fin 4) : d - row + row = d := by
  fin_cases d <;> fin_cases row <;> decide

theorem wordDiffusion_diagonal (x : State) (d : Fin 4) :
    (fun row => wordDiffusion x row (d - row)) =
      columnMatrix mixEntry (fun row => x row (d + row)) := by
  funext row
  change mixColumns (shiftRows x) row (d - row + row) = _
  rw [fin4_sub_add]
  exact congrFun (mixColumns_column (shiftRows x) d) row

/-- Equal numbers of free input columns and zero output columns force zero.
Each column has 2^32 values, but the proof uses only four byte MDS instances. -/
theorem wordDiffusion_mds_zero (r c : Fin 16) (hsize : maskSize r = maskSize c)
    (x : State) (hs : projectColumns c x = x)
    (hz : projectColumns r (wordDiffusion x) = 0) : x = 0 := by
  have hd (d : Fin 4) : (fun row => x row (d + row)) = 0 := by
    apply mixColumns_mds_zero (outputDiagonalMask r d) (inputDiagonalMask c d)
    · rw [outputDiagonalMask_size, inputDiagonalMask_size, hsize]
    · funext row
      change (if maskBit (inputDiagonalMask c d) row then x row (d + row) else 0) = _
      rw [inputDiagonalMask_bit]
      exact congrFun (congrFun hs row) (d + row)
    · rw [← wordDiffusion_diagonal]
      funext row
      change (if maskBit (outputDiagonalMask r d) row then
        wordDiffusion x row (d - row) else 0) = 0
      rw [outputDiagonalMask_bit]
      exact congrFun (congrFun hz row) (d - row)
  funext row col
  have he := congrFun (hd (col - row)) row
  simpa only [fin4_sub_add, Pi.zero_apply] using he

theorem wordDiffusion_injective : Function.Injective wordDiffusion :=
  shiftRows_injective.comp (mixColumns_injective.comp shiftRows_injective)

end AESMixing.AES
