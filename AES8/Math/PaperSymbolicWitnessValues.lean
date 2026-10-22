import AES8.Math.PaperSymbolicWitnessBase

noncomputable section
namespace AES8.PaperSymbolicShortening
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable PaperSymbolicMDS
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

theorem witness_first (pair : Bool) (k : Fin 20) :
    graphWord (X : P) (witness pair k) 4 = (raw pair k).2 := by
  fin_cases pair <;> fin_cases k <;>
    simp [witness, shapes, markedRow, graphWord, graphMatrix, matrix, inverse,
      raw, minor, secondMark, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] <;>
    ring_nf <;> (try simp)

theorem witness_second (pair : Bool) (k : Fin 20) :
    graphWord (X : P) (witness pair k) (secondMark pair) = (raw pair k).1 := by
  fin_cases pair <;> fin_cases k <;>
    simp [witness, shapes, markedRow, graphWord, graphMatrix, matrix, inverse,
      raw, minor, secondMark, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] <;>
    ring_nf <;> (try simp)


end AES8.PaperSymbolicShortening
