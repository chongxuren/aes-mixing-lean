import AES8.Math.PaperAlgebraicSpecialization
import AES8.Math.PaperSymbolicDiffusion
import AES8.Math.PaperSymbolicLabels
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.ComputeDegree

/-! The complete printed polynomial fractions, verified before specialization. -/
noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
open scoped Matrix CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev P := (ZMod 2)[X]

def raw (pair : Bool) (k : Fin 20) : P × P :=
  match shapes pair k with
  | .one i => (matrix X (markedRow pair) i, matrix X 0 i)
  | .two i j w => (minor X (markedRow pair) w i j, minor X 0 w i j)
  | .three i => (inverse X i 0, inverse X i (markedRow pair))

/-- Printed reduced numerator and denominator; order matches `triples`. -/
def printed (pair : Bool) : Fin 20 → P × P :=
  let a : P := X
  let b := X+1
  let c := X^2+X+1
  let d := X^3+X+1
  let e := X^3+X^2+1
  if pair then
    ![(d,b*c),(e,a*c),(a,c),(b,c),(b*c,d),(c,1),(1,c),(1,1),
      (a,b),(1,a),(a*c,e),(b,a),(1,1),(1,c),(c,1),(1,b),
      (c,b),(c,a),(a,1),(b,1)]
  else
    ![(d,e),(e,b*c),(1,1),(b,1),(b,a),(a^2,1),(1,b^2),(1,c),
      (a,c),(1,a),(a*c,d),(1,a),(1,1),(b^2,c),(c,a^2),(a,b),
      (c,b),(c,1),(b,1),(1,1)]

macro "symbolic_poly_ne" : tactic => `(tactic|
  (intro h
   first
   | have hc := congrArg (fun p : P => p.coeff 0) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 1) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 2) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 3) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 4) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 5) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
   | have hc := congrArg (fun p : P => p.coeff 6) h
     norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow, Finset.sum_range_succ] at hc
     done
  ))

theorem raw_bounds (pair : Bool) (k : Fin 20) :
    (raw pair k).1 ≠ 0 ∧ (raw pair k).2 ≠ 0 ∧
    (raw pair k).1.natDegree ≤ 3 ∧ (raw pair k).2.natDegree ≤ 3 := by
  fin_cases pair <;> fin_cases k <;>
    simp [raw, shapes, markedRow, matrix, inverse, minor, printed] <;>
    ring_nf <;> (try simp) <;>
    (repeat' apply And.intro) <;> first | (compute_degree!; done) | symbolic_poly_ne

theorem printed_bounds (pair : Bool) (k : Fin 20) :
    (printed pair k).1 ≠ 0 ∧ (printed pair k).2 ≠ 0 ∧
    (printed pair k).1.natDegree ≤ 3 ∧ (printed pair k).2.natDegree ≤ 3 := by
  fin_cases pair <;> fin_cases k <;>
    simp [raw, shapes, markedRow, matrix, inverse, minor, printed] <;>
    ring_nf <;> (try simp) <;>
    (repeat' apply And.intro) <;> first | (compute_degree!; done) | symbolic_poly_ne

theorem raw_printed (pair : Bool) (k : Fin 20) :
    (raw pair k).1 * (printed pair k).2 =
      (printed pair k).1 * (raw pair k).2 := by
  fin_cases pair <;> fin_cases k <;>
    simp [raw, shapes, markedRow, matrix, inverse, minor, printed] <;> ring_nf <;> simp


end AES8.PaperSymbolicSlopeTable
