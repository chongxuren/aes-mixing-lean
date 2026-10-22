import AES8.Math.PaperSymbolicWitnessBase

noncomputable section
namespace AES8.PaperSymbolicShortening
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable PaperSymbolicMDS
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

theorem witness_zero (pair : Bool) (k : Fin 20) (i : Fin 8)
    (hi : i ∈ zeros pair k) : graphWord (X : P) (witness pair k) i = 0 := by
  fin_cases pair <;> fin_cases k <;> fin_cases i <;>
    simp [zeros, marked, triples] at hi <;>
    simp [witness, shapes, markedRow, graphWord, graphMatrix, matrix, inverse,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] <;> ring_nf <;> (try simp)


end AES8.PaperSymbolicShortening
