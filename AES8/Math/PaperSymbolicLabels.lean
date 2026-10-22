import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace AES8.PaperSymbolicSlopeTable
open scoped Matrix
set_option autoImplicit false
set_option maxRecDepth 8192

inductive Shape where
  | one (i : Fin 4)
  | two (i j w : Fin 4)
  | three (i : Fin 4)
  deriving DecidableEq

/-- `false` is pair 45; `true` is pair 46. The smaller marked output is 4. -/
def markedRow (pair : Bool) : Fin 4 := if pair then 2 else 1

def triples (pair : Bool) : Fin 20 → Finset (Fin 8) :=
  if pair then
    ![{0,1,2},{0,1,3},{0,1,5},{0,1,7},{0,2,3},{0,2,5},{0,2,7},
      {0,3,5},{0,3,7},{0,5,7},{1,2,3},{1,2,5},{1,2,7},{1,3,5},
      {1,3,7},{1,5,7},{2,3,5},{2,3,7},{2,5,7},{3,5,7}]
  else
    ![{0,1,2},{0,1,3},{0,1,6},{0,1,7},{0,2,3},{0,2,6},{0,2,7},
      {0,3,6},{0,3,7},{0,6,7},{1,2,3},{1,2,6},{1,2,7},{1,3,6},
      {1,3,7},{1,6,7},{2,3,6},{2,3,7},{2,6,7},{3,6,7}]

def shapes (pair : Bool) : Fin 20 → Shape :=
  let w : Fin 4 := if pair then 1 else 2
  ![.three 3,.three 2,.two 0 1 3,.two 0 1 w,.three 1,.two 0 2 3,
    .two 0 2 w,.two 0 3 3,.two 0 3 w,.one 0,.three 0,.two 1 2 3,
    .two 1 2 w,.two 1 3 3,.two 1 3 w,.one 1,.two 2 3 3,.two 2 3 w,
    .one 2,.one 3]

/-- Canonical equality-class labels, with exactly the printed coincidences. -/
def slopeClass (pair : Bool) : Fin 20 → Fin 20 :=
  if pair then ![0,1,2,3,4,5,6,7,8,9,10,11,7,6,5,12,13,14,15,16]
  else ![0,1,2,3,4,5,6,7,8,9,10,9,2,11,12,13,14,15,3,2]

def marked (pair : Bool) : Finset (Fin 8) := if pair then {4,6} else {4,5}
def zeros (pair : Bool) (k : Fin 20) : Finset (Fin 8) :=
  Finset.univ \ (marked pair ∪ triples pair k)

theorem triples_complete (pair : Bool) (s : Finset (Fin 8)) :
    s.card = 3 ∧ Disjoint s (marked pair) ↔ ∃ k, triples pair k = s := by
  fin_cases pair <;> revert s <;> decide

theorem triples_injective (pair : Bool) : Function.Injective (triples pair) := by
  fin_cases pair <;> decide

theorem zeros_card (pair : Bool) (k : Fin 20) : (zeros pair k).card = 3 := by
  fin_cases pair <;> fin_cases k <;> decide

theorem class_count45 : (Finset.univ.image (slopeClass false)).card = 16 := by decide
theorem class_count46 : (Finset.univ.image (slopeClass true)).card = 17 := by decide


end AES8.PaperSymbolicSlopeTable
