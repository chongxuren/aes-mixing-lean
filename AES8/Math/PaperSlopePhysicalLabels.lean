import AES8.Math.PaperSlopeCoincidences

/-!
# Physical positions of the six marked pairs

The paper labels its graph by inputs 0--3 and outputs 4--7.  These
definitions rotate both halves together.  The orientation of pair 74 is
cyclic; this avoids changing the representative slope into its reciprocal.
Only finite coordinate bookkeeping is proved here.
-/
namespace AES8.PaperSlopePhysicalLabels
open PaperSymbolicSlopeTable PaperSlopeCoincidences
set_option autoImplicit false
set_option maxRecDepth 100000

def rotate (r : ℕ) (i : Fin 8) : Fin 8 :=
  if i.val < 4 then ⟨(i.val+r)%4, by omega⟩
  else ⟨4+(i.val-4+r)%4, by omega⟩

def firstMark (p : Fin 6) : Fin 8 := rotate (rotation p) 4
def secondMark (p : Fin 6) : Fin 8 :=
  rotate (rotation p) (if pairType p then 6 else 5)
def marks (p : Fin 6) : Finset (Fin 8) := {firstMark p, secondMark p}
def uniform (p : Fin 6) (k : Fin 20) : Finset (Fin 8) :=
  (triples (pairType p) k).image (rotate (rotation p))
def zeros (p : Fin 6) (k : Fin 20) : Finset (Fin 8) :=
  (marks p ∪ uniform p k)ᶜ

theorem marks_distinct (p : Fin 6) : firstMark p ≠ secondMark p := by
  fin_cases p <;> decide

theorem marks_card (p : Fin 6) : (marks p).card = 2 := by
  fin_cases p <;> decide

theorem marks_outputs (p : Fin 6) : ∀ i ∈ marks p, 4 ≤ i.val := by
  fin_cases p <;> decide

theorem all_six_pairs (s : Finset (Fin 8)) :
    s.card = 2 ∧ (∀ i ∈ s, 4 ≤ i.val) ↔ ∃ p, marks p = s := by
  revert s
  decide

theorem marks_injective : Function.Injective marks := by decide

theorem uniform_card (p : Fin 6) (k : Fin 20) : (uniform p k).card = 3 := by
  fin_cases p <;> fin_cases k <;> decide

theorem uniform_disjoint (p : Fin 6) (k : Fin 20) :
    Disjoint (marks p) (uniform p k) := by
  fin_cases p <;> fin_cases k <;> decide

theorem uniform_injective (p : Fin 6) : Function.Injective (uniform p) := by
  fin_cases p <;> decide

theorem all_twenty_triples (p : Fin 6) (s : Finset (Fin 8)) :
    s.card = 3 ∧ Disjoint (marks p) s ↔ ∃ k, uniform p k = s := by
  fin_cases p <;> revert s <;> decide

theorem zeros_card (p : Fin 6) (k : Fin 20) : (zeros p k).card = 3 := by
  fin_cases p <;> fin_cases k <;> decide

theorem zeros_representative (p : Fin 6) (k : Fin 20) :
    zeros p k = (PaperSymbolicSlopeTable.zeros (pairType p) k).image
      (rotate (rotation p)) := by
  fin_cases p <;> fin_cases k <;> decide

def inputPart (s : Finset (Fin 8)) : Finset (Fin 4) :=
  (s.filter (fun i => i.val < 4)).image
    (fun i => (⟨i.val%4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
def outputPart (s : Finset (Fin 8)) : Finset (Fin 8) :=
  s.filter (fun i => 4 ≤ i.val)
def outputDifference (s t : Finset (Fin 8)) : ℕ :=
  ((outputPart s \ outputPart t) ∪ (outputPart t \ outputPart s)).card

/-- The analytic matrix's input labels are the literal rotated input legs. -/
theorem inputPart_eq (p : Fin 6) (k : Fin 20) :
    inputPart (uniform p k) = inputSet p k := by
  fin_cases p <;> fin_cases k <;> decide

/-- Rotating the physical output legs preserves the metric distance. -/
theorem outputDifference_eq (p : Fin 6) (k l : Fin 20) :
    outputDifference (uniform p k) (uniform p l) = outputDistance p k l := by
  fin_cases p <;> fin_cases k <;> fin_cases l <;> decide

end AES8.PaperSlopePhysicalLabels
