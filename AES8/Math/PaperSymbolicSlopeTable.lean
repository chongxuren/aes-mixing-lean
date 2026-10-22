import AES8.Math.PaperSymbolicSlopePrinted

noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
set_option autoImplicit false
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

set_option maxHeartbeats 200000 in
theorem slope_eq_iff (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (i j : Fin 20) :
    slope a pair i = slope a pair j ↔ slopeClass pair i = slopeClass pair j := by
  unfold slope
  exact (PaperAlgebraicSpecialization.cubic_ratio_eq_iff (K := ZMod 2) (F := F) a ha
    (raw pair i).1 (raw pair i).2 (raw pair j).1 (raw pair j).2
    (raw_bounds pair i).2.2.1 (raw_bounds pair i).2.2.2
    (raw_bounds pair j).2.2.1 (raw_bounds pair j).2.2.2
    (raw_bounds pair i).2.1 (raw_bounds pair j).2.1).trans (cross_class pair i j)

end AES8.PaperSymbolicSlopeTable
