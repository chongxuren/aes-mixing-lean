import AES8.Math.PaperSymbolicWitnessZero
import AES8.Math.PaperSymbolicWitnessValues

noncomputable section
namespace AES8.PaperSymbolicShortening
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable PaperSymbolicMDS
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

theorem first_zero_set_card (pair : Bool) (k : Fin 20) :
    (insert 4 (zeros pair k)).card = 4 := by
  fin_cases pair <;> fin_cases k <;> decide


end AES8.PaperSymbolicShortening
