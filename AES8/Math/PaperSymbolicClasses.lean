import AES8.Math.PaperSymbolicClasses4500
import AES8.Math.PaperSymbolicClasses4510
import AES8.Math.PaperSymbolicClasses4600
import AES8.Math.PaperSymbolicClasses4610

noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
set_option autoImplicit false

theorem cross_class (pair : Bool) (i j : Fin 20) :
    (raw pair i).1 * (raw pair j).2 = (raw pair j).1 * (raw pair i).2 ↔
      slopeClass pair i = slopeClass pair j := by
  refine Fin.addCases (m := 10) (n := 10) ?_ ?_ i
  · intro k
    cases pair
    · exact cross_class45_0 k j
    · exact cross_class46_0 k j
  · intro k
    cases pair
    · exact cross_class45_10 k j
    · exact cross_class46_10 k j


end AES8.PaperSymbolicSlopeTable
