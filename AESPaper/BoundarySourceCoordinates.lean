import AESPaper.BoundaryZeros
import AESPaper.ByteCoordinateTransport
import AESConcrete.SingleByteCoordinates

/-!
# Actual single-word source coordinates at the AES boundary

The input is one arbitrary 32-bit word at physical word position k. For
output word c and byte r, the source byte is k-c-r and its multiplier is
the actual MixColumns coefficient mixEntry r (k-c-r). Each output word
is therefore a byte-position permutation followed by zero-fixing byte
permutations, exactly in ByteCoordinateTransport's interface.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.BoundarySourceCoordinates
open AESMixing AESMixing.AES
open AESConcrete.WordColumnGram (singleByteWord)
open AESConcrete.SingleByteCoordinates (coordinatePerm coordinatePerm_apply coordinatePerm_zero)

/-- Insert a whole source word into its actual four-word input position. -/
def singleWord (k : Fin 4) (x : AES.Word) : AES.WordState :=
  fun c => if c = k then x else 0

theorem singleWord_same (k : Fin 4) (x : AES.Word) : singleWord k x k = x := by
  simp [singleWord]

theorem singleWord_other (k c : Fin 4) (h : c ≠ k) (x : AES.Word) :
    singleWord k x c = 0 := by simp [singleWord, h]

/-- Only four coordinate labels are checked; no byte values are enumerated. -/
theorem source_index_iff : ∀ k c r i : Fin 4,
    (c+r)+i = k ↔ i = k-c-r := by decide

theorem output_column_index : ∀ c r : Fin 4, (c+r)-r = c := by decide

theorem position_involutive : ∀ k c r : Fin 4,
    k-c-(k-c-r) = r := by decide

/-- Actual reindexing of the source bytes in output word c. -/
def positionPerm (k c : Fin 4) : Equiv.Perm (Fin 4) where
  toFun r := k-c-r
  invFun r := k-c-r
  left_inv r := position_involutive k c r
  right_inv r := position_involutive k c r

theorem positionPerm_apply (k c r : Fin 4) : positionPerm k c r = k-c-r := rfl

/-- The selected physical diagonal is exactly a one-byte input column. -/
theorem source_column (k c r : Fin 4) (x : AES.Word) :
    (fun i => transposeState (singleWord k x) i ((c+r)+i)) =
      singleByteWord (k-c-r) (x (k-c-r)) := by
  funext i
  have hc := source_index_iff k c r i
  by_cases hi : i = k-c-r
  · have hk : (c+r)+i = k := hc.mpr hi
    simp [transposeState, singleWord, singleByteWord, hk, hi]
  · have hk : (c+r)+i ≠ k := fun h => hi (hc.mp h)
    simp [transposeState, singleWord, singleByteWord, hk, hi]

/-- Pointwise identification before any norm or law transport is applied. -/
theorem boundary_singleWord_apply (k c r : Fin 4) (x : AES.Word) :
    GroupedRecurrence.boundary (singleWord k x) c r =
      coordinatePerm false (k-c-r) r (x (k-c-r)) := by
  have hb : GroupedRecurrence.boundary (singleWord k x) c r =
      AES.wordMix (singleWord k x) c r :=
    congrArg (fun y : AES.WordState => y c r) (BoundaryZeros.boundary_wordMix (singleWord k x))
  have hw := AES.wordMix_apply (singleWord k x) c r
  have hd := congrFun (wordDiffusion_diagonal (transposeState (singleWord k x)) (c+r)) r
  rw [output_column_index] at hd
  have hi := source_column k c r x
  have hc : columnMatrix mixEntry
      (fun i => transposeState (singleWord k x) i ((c+r)+i)) r =
      columnMatrix mixEntry (singleByteWord (k-c-r) (x (k-c-r))) r :=
    congrArg (fun z : AES.Word => columnMatrix mixEntry z r) hi
  have hp : coordinatePerm false (k-c-r) r (x (k-c-r)) =
      columnMatrix mixEntry (singleByteWord (k-c-r) (x (k-c-r))) r := rfl
  exact hb.trans (hw.trans (hd.trans (hc.trans hp.symm)))

/-- Each coordinate permutation is the actual nonzero MixColumns scalar. -/
theorem coordinatePerm_mul (j r : Fin 4) (t : BinaryWord 8) :
    coordinatePerm false j r t = (⟨mixEntry r j⟩ : BinaryWord 8) * t := by
  rw [coordinatePerm_apply, byteDiffusionOrientation_apply]
  change (∑ i : Fin 4, gramMixing false r i * singleByteWord j t i) = _
  simp [gramMixing, singleByteWord, mul_ite]

theorem mixEntry_nonzero (r j : Fin 4) : (⟨mixEntry r j⟩ : BinaryWord 8) ≠ 0 := by
  fin_cases r <;> fin_cases j <;> decide

theorem boundary_singleWord_mul (k c r : Fin 4) (x : AES.Word) :
    GroupedRecurrence.boundary (singleWord k x) c r =
      (⟨mixEntry r (k-c-r)⟩ : BinaryWord 8) * x (k-c-r) := by
  exact (boundary_singleWord_apply k c r x).trans (coordinatePerm_mul (k-c-r) r (x (k-c-r)))

/-- Actual zero-fixing byte value permutation, with the source byte identified. -/
def bytePerm (k c r : Fin 4) : Equiv.Perm (BinaryWord 8) :=
  coordinatePerm false (k-c-r) r

theorem bytePerm_zero (k c r : Fin 4) : bytePerm k c r 0 = 0 :=
  coordinatePerm_zero false (k-c-r) r

def outputEquiv (k c : Fin 4) : Equiv.Perm AES.Word :=
  ByteCoordinateTransport.coordinateEquiv (positionPerm k c) (bytePerm k c)

theorem outputEquiv_apply (k c r : Fin 4) (x : AES.Word) :
    outputEquiv k c x r = (⟨mixEntry r (k-c-r)⟩ : BinaryWord 8) * x (k-c-r) := by
  exact coordinatePerm_mul (k-c-r) r (x (k-c-r))

/-- The coordinate equivalence is the complete actual output word. -/
theorem boundary_singleWord (k c : Fin 4) (x : AES.Word) :
    GroupedRecurrence.boundary (singleWord k x) c = outputEquiv k c x := by
  funext r
  exact boundary_singleWord_apply k c r x

theorem outputEquiv_zero (k c : Fin 4) : outputEquiv k c 0 = 0 :=
  ByteCoordinateTransport.coordinateEquiv_const (positionPerm k c) (bytePerm k c)
    (0 : BinaryWord 8) (bytePerm_zero k c)

/-- A nonzero source word produces four nonzero output words. -/
theorem boundary_singleWord_allActive (k : Fin 4) (x : AES.Word) (hx : x ≠ 0)
    (c : Fin 4) : GroupedRecurrence.boundary (singleWord k x) c ≠ 0 := by
  rw [boundary_singleWord]
  intro h
  exact hx ((outputEquiv k c).injective (h.trans (outputEquiv_zero k c).symm))

/-- Byte-degree projections transport exactly; the input weights may be joint. -/
theorem degree_energy_outputEquiv (k c : Fin 4) (j : Fin 5) (f : AES.Word → ℝ) :
    (∑ y : AES.Word, degreeComponent (0 : BinaryWord 8) j
      (lawRelabel (outputEquiv k c) f) y ^ 2) =
      ∑ y : AES.Word, degreeComponent (0 : BinaryWord 8) j f y ^ 2 :=
  ByteCoordinateTransport.degree_energy_transport (positionPerm k c) (bytePerm k c)
    (0 : BinaryWord 8) (bytePerm_zero k c) j f

theorem uniformExcept_outputEquiv (k c : Fin 4) :
    lawRelabel (outputEquiv k c) (uniformExcept (0 : AES.Word)) = uniformExcept 0 :=
  ByteCoordinateTransport.uniformExcept_transport (positionPerm k c) (bytePerm k c)
    (0 : BinaryWord 8) (bytePerm_zero k c)

end AESPaper.BoundarySourceCoordinates
