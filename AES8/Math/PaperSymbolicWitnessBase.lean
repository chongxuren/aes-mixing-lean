import AES8.Math.PaperSymbolicGraph

/-! Actual shortened graph lines for all twenty triples per marked pair.
Witnesses satisfy the three physical zero constraints. MDS uniqueness then
identifies the entire marked-coordinate image, not just one witness ratio. -/
noncomputable section
namespace AES8.PaperSymbolicShortening
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable PaperSymbolicMDS
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

def secondMark (pair : Bool) : Fin 8 := if pair then 6 else 5

/-- An unnormalized kernel vector for the actual three-zero constraints. -/
def witness (pair : Bool) (k : Fin 20) : Fin 4 → P :=
  match shapes pair k with
  | .one i => fun j => if j=i then 1 else 0
  | .two i j w => fun l =>
      (if l=i then matrix X w j else 0) + (if l=j then matrix X w i else 0)
  | .three i => fun j =>
      inverse X j 0 * inverse X i (markedRow pair) +
      inverse X j (markedRow pair) * inverse X i 0


end AES8.PaperSymbolicShortening
