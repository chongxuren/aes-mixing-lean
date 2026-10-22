import AES8.Math.PaperSymbolicSlopeDef

noncomputable section
namespace AES8.PaperSymbolicSlopeTable
open Polynomial PaperSymbolicDiffusion
set_option autoImplicit false
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

set_option maxHeartbeats 200000 in
theorem slope_eq_printed (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (k : Fin 20) :
    slope a pair k = aeval a (printed pair k).1 / aeval a (printed pair k).2 := by
  unfold slope
  exact (PaperAlgebraicSpecialization.cubic_ratio_eq_iff (K := ZMod 2) (F := F) a ha
    (raw pair k).1 (raw pair k).2 (printed pair k).1 (printed pair k).2
    (raw_bounds pair k).2.2.1 (raw_bounds pair k).2.2.2
    (printed_bounds pair k).2.2.1 (printed_bounds pair k).2.2.2
    (raw_bounds pair k).2.1 (printed_bounds pair k).2.1).2 (raw_printed pair k)


end AES8.PaperSymbolicSlopeTable
