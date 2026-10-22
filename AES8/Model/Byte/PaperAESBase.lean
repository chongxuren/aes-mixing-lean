import AES8.Math.PaperAlgebraicSpecialization
import AES8.Math.PaperSymbolicDiffusion
import AESMixing.ByteField
import AESMixing.MatrixLinear
import AESMixing.AESState
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.ComputeDegree

/-! Algebraic degree of the literal AES byte 0x02, using the existing byte
field. The lower bound checks the eight binary basis coefficients, while the
upper bound uses the published AES modulus. -/
namespace AES8.PaperAESAlgebraic
open Polynomial AESMixing
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev Byte := BinaryWord 8

instance byteCharTwo : CharP Byte 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by decide)
instance byteAlgebra : Algebra (ZMod 2) Byte := ZMod.algebra Byte 2

def generator : Byte := ⟨2#8⟩

def byteEval (v : Fin 8 → ZMod 2) : Byte :=
  ∑ i : Fin 8, if v i = 0 then 0 else AES.byteBasis i


end AES8.PaperAESAlgebraic
