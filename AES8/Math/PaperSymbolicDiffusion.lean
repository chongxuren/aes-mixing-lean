import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The printed characteristic-two diffusion matrix and its polynomial inverse.
These identities precede evaluation and apply over every characteristic-two
commutative ring. Nonzero minors and slope classification are separate. -/
noncomputable section
open scoped Matrix BigOperators CharTwo
namespace AES8.PaperSymbolicDiffusion
set_option autoImplicit false
variable {R : Type*} [CommRing R] [CharP R 2]

def matrix (t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![t,t+1,1,1; 1,t,t+1,1; 1,1,t,t+1; t+1,1,1,t]

def inverse (t : R) : Matrix (Fin 4) (Fin 4) R :=
  let a := t*(t^2+t+1)
  let b := t^3+t+1
  let c := t^3+t^2+1
  let d := (t+1)*(t^2+t+1)
  !![a,b,c,d; d,a,b,c; c,d,a,b; b,c,d,a]

theorem matrix_mul_inverse (t : R) : matrix t * inverse t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, inverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp

theorem inverse_mul_matrix (t : R) : inverse t * matrix t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, inverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp

def minor (t : R) (u v i j : Fin 4) : R :=
  matrix t u i * matrix t v j + matrix t u j * matrix t v i

def columnPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

theorem adjacent_minors (t : R) (k : Fin 6) :
    minor t 0 1 (columnPair k).1 (columnPair k).2 =
      ![t^2+t+1,t^2+t+1,t+1,t^2+t+1,1,t] k := by
  fin_cases k <;> simp [minor, matrix, columnPair] <;> ring_nf <;> simp

theorem opposite_minors (t : R) (k : Fin 6) :
    minor t 0 2 (columnPair k).1 (columnPair k).2 =
      ![1,(t+1)^2,t^2+t+1,t^2+t+1,t^2,1] k := by
  fin_cases k <;> simp [minor, matrix, columnPair] <;> ring_nf <;> simp

end AES8.PaperSymbolicDiffusion
