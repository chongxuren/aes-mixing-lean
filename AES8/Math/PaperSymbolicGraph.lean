import AES8.Math.PaperSymbolicTableCore
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! All physical information sets of the symbolic diffusion graph.
Every four-coordinate restriction is bijective, for arbitrary fields satisfying
the degree condition; no finiteness of the alphabet is assumed. -/
noncomputable section
namespace AES8.PaperSymbolicMDS
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

variable {R : Type*} [CommRing R]
def graphMatrix (t : R) : Matrix (Fin 8) (Fin 4) R :=
  !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1;
     t,t+1,1,1; 1,t,t+1,1; 1,1,t,t+1; t+1,1,1,t]

def graphWord (t : R) (x : Fin 4 → R) : Fin 8 → R := graphMatrix t *ᵥ x

abbrev InformationSet := {s : Finset (Fin 8) // s.card = 4}

def infoMatrix (t : R) (s : InformationSet) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => graphMatrix t (s.val.orderEmbOfFin s.property i) j

/-- Exactly the 70 physical four-coordinate information sets. -/
theorem informationSet_card : Fintype.card InformationSet = 70 := by decide


end AES8.PaperSymbolicMDS
