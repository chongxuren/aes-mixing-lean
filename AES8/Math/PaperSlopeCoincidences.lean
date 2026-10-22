import AES8.Math.PaperSymbolicLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual graph-label coincidence counts in the degree-two argument

The four adjacent marked pairs and two opposite marked pairs are obtained by
literal cyclic rotation of the paper's two representative tables. Only class
labels enter this count; their identification with actual field slopes belongs
to the symbolic-geometry theorem. No independent numerical AES slope table is
introduced here.
-/
open scoped BigOperators
namespace AES8.PaperSlopeCoincidences
open PaperSymbolicSlopeTable
set_option autoImplicit false
set_option maxRecDepth 100000

def pairType (p : Fin 6) : Bool := decide (4 ≤ p.val)
def rotation (p : Fin 6) : ℕ := if p.val < 4 then p.val else p.val-4

def inputSet (p : Fin 6) (k : Fin 20) : Finset (Fin 4) :=
  ((triples (pairType p) k).filter (fun i => i.val < 4)).image
    (fun i => (⟨(i.val + rotation p)%4, Nat.mod_lt _ (by decide)⟩ : Fin 4))

def outputSet (p : Fin 6) (k : Fin 20) : Finset (Fin 8) :=
  (triples (pairType p) k).filter (fun i => 4 ≤ i.val)

def outputDistance (p : Fin 6) (k l : Fin 20) : ℕ :=
  ((outputSet p k \ outputSet p l) ∪ (outputSet p l \ outputSet p k)).card

def group (A : Finset (Fin 4)) : Fin 2 := if A.card = 2 then 1 else 0
def opposite (A : Finset (Fin 4)) : Prop := A = {0,2} ∨ A = {1,3}
instance (A : Finset (Fin 4)) : Decidable (opposite A) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Number of coincident ordered contraction pairs with this input row,
target group and output symmetric-difference size. -/
def count (A : Finset (Fin 4)) (g : Fin 2) (d : Fin 3) : ℕ :=
  ∑ p : Fin 6, ∑ k : Fin 20,
    if inputSet p k = A then
      ∑ l : Fin 20,
        if slopeClass (pairType p) k = slopeClass (pairType p) l ∧
            group (inputSet p l) = g ∧ outputDistance p k l = d.val then 1 else 0
    else 0

def printedCount (A : Finset (Fin 4)) (g : Fin 2) (d : Fin 3) : ℕ :=
  if A.card = 1 then
    if g = 0 ∧ d = 0 then 6 else if g = 1 ∧ d = 1 then 4 else 0
  else if A.card = 2 then
    if g = 1 ∧ d = 0 then 12
    else if g = 1 ∧ d = 2 then (if opposite A then 4 else 3)
    else if g = 0 ∧ d = 1 ∧ ¬opposite A then 4 else 0
  else if A.card = 3 ∧ g = 0 ∧ d = 0 then 6 else 0

theorem input_card (p : Fin 6) (k : Fin 20) :
    1 ≤ (inputSet p k).card ∧ (inputSet p k).card ≤ 3 := by
  fin_cases p <;> fin_cases k <;> decide

theorem output_distance_le (p : Fin 6) (k l : Fin 20) :
    outputDistance p k l ≤ 2 := by
  fin_cases p <;> fin_cases k <;> fin_cases l <;> decide

theorem row_counts (A : Finset (Fin 4)) (g : Fin 2) (d : Fin 3) :
    count A g d = printedCount A g d := by
  revert A
  fin_cases g <;> fin_cases d <;> decide

end AES8.PaperSlopeCoincidences
