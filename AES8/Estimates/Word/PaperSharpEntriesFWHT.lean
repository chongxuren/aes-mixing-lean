import AES8.Estimates.Word.PaperSharpEntriesFinite
import Mathlib.LinearAlgebra.Pi

/-!
# Fixed 256-coordinate fast Walsh transform

Draft only. A single fixed linear operator is verified against the actual
AES trace pairing on integer coordinate basis vectors. Subsequent certificates
can reuse that theorem rather than re-prove a transform identity for each map.
No result of a compiled native checker is admitted as a premise.
-/

open scoped BigOperators

namespace AES8.PaperSharpEntriesFWHT
open AESMixing
open AES8.PaperSharpEntriesFinite (Byte)

abbrev Index := Fin 256
abbrev Vector := Index → ℤ

set_option autoImplicit false
set_option maxRecDepth 65536

def byteOf (i : Index) : Byte := ⟨BitVec.ofFin i⟩

def flip (stage : Fin 8) (i : Index) : Index :=
  ((BitVec.ofFin i : BitVec 8) ^^^ BitVec.ofNat 8 (2^stage.val)).toFin

/-- One radix-two butterfly layer, as an integer linear map. -/
def butterfly (stage : Fin 8) : Vector →ₗ[ℤ] Vector where
  toFun f i :=
    if (BitVec.ofFin i : BitVec 8).getLsbD stage.val
      then f (flip stage i) - f i
      else f i + f (flip stage i)
  map_add' f g := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' z f := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- Layers are applied from bit zero through bit seven. -/
def transform : Vector →ₗ[ℤ] Vector :=
  (butterfly 7).comp ((butterfly 6).comp ((butterfly 5).comp
    ((butterfly 4).comp ((butterfly 3).comp ((butterfly 2).comp
      ((butterfly 1).comp (butterfly 0)))))))

/-- Coordinates of the actual trace character as an ordinary bit-dot mask. -/
def traceIndex (k : Byte) : Index :=
  (BitVec.ofNat 8 (∑ i : Fin 8,
    if AES.traceBit (AES.mul k.bits (AES.byteBasis i).bits) then 2^i.val else 0)).toFin

def sign (k x : Byte) : ℤ := if AES.traceBit (AES.mul k.bits x.bits) then -1 else 1

def basisVector (i : Index) : Vector := Pi.single i 1

/-- The fixed finite transform correspondence obligation. The separate
certificate module proves it; checker soundness remains independent of the
cost and sharding of that finite verification. -/
def CoefficientSpec : Prop := ∀ i k : Index,
  transform (basisVector i) (traceIndex (byteOf k)) = sign (byteOf k) (byteOf i)

theorem transform_trace_formula (hcoeff : CoefficientSpec) (f : Vector) (k : Byte) :
    transform f (traceIndex k) = ∑ i : Index, sign k (byteOf i) * f i := by
  have hf : f = ∑ i : Index, f i • basisVector i := by
    funext j
    simp [basisVector, Pi.single_apply]
  calc
    _ = transform (∑ i : Index, f i • basisVector i) (traceIndex k) :=
      congrArg (fun v : Vector => transform v (traceIndex k)) hf
    _ = ∑ i : Index, f i * transform (basisVector i) (traceIndex k) := by
      simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hk : byteOf k.bits.toFin = k := by cases k; rfl
      have he := hcoeff i k.bits.toFin
      rw [hk] at he
      rw [he]
      ring

/-- An optional literal stage transcript keeps production kernel work linear
in the 2048 coordinate checks, without relying on evaluator sharing of nested
function applications. Transcript entries are ordinary integer data. -/
abbrev StageTables := Fin 9 → Array ℤ

def stageVector (stages : StageTables) (s : Fin 9) : Vector :=
  fun i => (stages s)[i.val]!

def checkStages (stages : StageTables) : Bool :=
  decide (∀ s : Fin 8, ∀ i : Index,
    stageVector stages ⟨s.val+1, by omega⟩ i =
      butterfly s (stageVector stages ⟨s.val, by omega⟩) i)

theorem checkStages_sound (stages : StageTables) (hc : checkStages stages = true) :
    stageVector stages 8 = transform (stageVector stages 0) := by
  have he := of_decide_eq_true hc
  have hstep (s : Fin 8) :
      stageVector stages ⟨s.val+1, by omega⟩ =
        butterfly s (stageVector stages ⟨s.val, by omega⟩) := by
    funext i
    exact he s i
  have h0 : stageVector stages 1 = butterfly 0 (stageVector stages 0) := by
    simpa using hstep 0
  have h1 : stageVector stages 2 = butterfly 1 (stageVector stages 1) := by
    simpa using hstep 1
  have h2 : stageVector stages 3 = butterfly 2 (stageVector stages 2) := by
    simpa using hstep 2
  have h3 : stageVector stages 4 = butterfly 3 (stageVector stages 3) := by
    simpa using hstep 3
  have h4 : stageVector stages 5 = butterfly 4 (stageVector stages 4) := by
    simpa using hstep 4
  have h5 : stageVector stages 6 = butterfly 5 (stageVector stages 5) := by
    simpa using hstep 5
  have h6 : stageVector stages 7 = butterfly 6 (stageVector stages 6) := by
    simpa using hstep 6
  have h7 : stageVector stages 8 = butterfly 7 (stageVector stages 7) := by
    simpa using hstep 7
  rw [h7,h6,h5,h4,h3,h2,h1,h0]
  rfl

def checkInitial (stages : StageTables) (f : Vector) : Bool :=
  decide (∀ i : Index, stageVector stages 0 i = f i)

theorem checkInitial_sound (stages : StageTables) (f : Vector)
    (hc : checkInitial stages f = true) : stageVector stages 0 = f := by
  funext i
  exact (of_decide_eq_true hc) i

theorem transcript_transform (stages : StageTables) (f : Vector)
    (hinitial : checkInitial stages f = true) (hsteps : checkStages stages = true) :
    stageVector stages 8 = transform f := by
  rw [checkStages_sound stages hsteps, checkInitial_sound stages f hinitial]

end AES8.PaperSharpEntriesFWHT
