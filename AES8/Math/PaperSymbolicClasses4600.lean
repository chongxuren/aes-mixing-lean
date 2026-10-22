import AES8.Math.PaperSymbolicTableCore

noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
open scoped Matrix CharTwo
set_option maxRecDepth 8192

theorem cross_class46_0 (i : Fin 10) (j : Fin 20) :
    (raw true (i.castAdd 10)).1 * (raw true j).2 =
      (raw true j).1 * (raw true (i.castAdd 10)).2 ↔
        slopeClass true (i.castAdd 10) = slopeClass true j := by
  fin_cases i <;> fin_cases j <;>
    simp [raw, shapes, markedRow, matrix, inverse, minor, slopeClass] <;>
    ring_nf <;> (try simp) <;> first | symbolic_poly_ne | (ring; done)

end AES8.PaperSymbolicSlopeTable
