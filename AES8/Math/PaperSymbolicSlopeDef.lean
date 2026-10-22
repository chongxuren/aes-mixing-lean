import Mathlib.Algebra.Field.ZMod
import AES8.Math.PaperSymbolicClasses

noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
set_option autoImplicit false

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

def slope (a : F) (pair : Bool) (k : Fin 20) : F :=
  aeval a (raw pair k).1 / aeval a (raw pair k).2


end AES8.PaperSymbolicSlopeTable
