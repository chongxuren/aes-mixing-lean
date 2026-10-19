import AESPaper.RawBoundaryCases
import AESPaper.RawBoundaryRounding
import AESPaper.RawBoundaryDegree
import AESPaper.ResidualMatrix

/-!
# Actual unscaled boundary C and t tables
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace AESPaper.RawBoundaryTable
open AESPaper.ProfileSpace
open AESPaper.BoundaryContraction (boundaryLayer)
open AESPaper.RawBoundaryRounding

theorem C_symmetric (i j : Fin 4) : Assembly.C i j = Assembly.C j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem boundary_C11 (f : ProfileSpace.State) :
    ‖component 1 (boundaryLayer (component 1 f))‖ ≤
      Assembly.C 0 0 * ‖component 1 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 1 1 raw11 _
    raw11_nonnegative ?_ ?_ f
  · exact round11
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw11, raw11, hq] using
      RawBoundaryCases.markedKernel_bound11 m hO hI

theorem boundary_C12 (f : ProfileSpace.State) :
    ‖component 1 (boundaryLayer (component 2 f))‖ ≤
      Assembly.C 0 1 * ‖component 2 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 1 2 raw12 _
    raw12_nonnegative ?_ ?_ f
  · exact round12
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw12, raw12, hq] using
      RawBoundaryCases.markedKernel_bound12 m hO hI

theorem boundary_C21 (f : ProfileSpace.State) :
    ‖component 2 (boundaryLayer (component 1 f))‖ ≤
      Assembly.C 1 0 * ‖component 1 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 2 1 raw12 _
    raw12_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 2 1 raw12 ≤ Assembly.C 1 0
    rw [ResidualMatrix.coefficient_comm 2 1, C_symmetric 1 0]
    exact round12
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw12, raw12, hq] using
      RawBoundaryCases.markedKernel_bound21 m hO hI

theorem boundary_C13 (f : ProfileSpace.State) :
    ‖component 1 (boundaryLayer (component 3 f))‖ ≤
      Assembly.C 0 2 * ‖component 3 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 1 3 raw13 _
    raw13_nonnegative ?_ ?_ f
  · exact round13
  · intro m hO hI
    simpa [RawBoundaryCases.raw13, raw13] using
      RawBoundaryCases.markedKernel_bound13 m hO hI

theorem boundary_C31 (f : ProfileSpace.State) :
    ‖component 3 (boundaryLayer (component 1 f))‖ ≤
      Assembly.C 2 0 * ‖component 1 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 3 1 raw13 _
    raw13_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 3 1 raw13 ≤ Assembly.C 2 0
    rw [ResidualMatrix.coefficient_comm 3 1, C_symmetric 2 0]
    exact round13
  · intro m hO hI
    simpa [RawBoundaryCases.raw13, raw13] using
      RawBoundaryCases.markedKernel_bound31 m hO hI

theorem boundary_C22 (f : ProfileSpace.State) :
    ‖component 2 (boundaryLayer (component 2 f))‖ ≤
      Assembly.C 1 1 * ‖component 2 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 2 2 raw22 _
    raw22_nonnegative ?_ ?_ f
  · exact round22
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw22, raw22, hq] using
      RawBoundaryCases.markedKernel_bound22 m hO hI

theorem boundary_t20 (f : ProfileSpace.State) :
    ‖component 2 (boundaryLayer (component 0 f))‖ ≤
      Assembly.t 1 * ‖component 0 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 2 0 raw2 _
    raw2_nonnegative ?_ ?_ f
  · exact round20
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw2, raw2, hq] using
      RawBoundaryCases.markedKernel_bound20 m hO hI

theorem boundary_t02 (f : ProfileSpace.State) :
    ‖component 0 (boundaryLayer (component 2 f))‖ ≤
      Assembly.t 1 * ‖component 2 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 0 2 raw2 _
    raw2_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 0 2 raw2 ≤ Assembly.t 1
    rw [ResidualMatrix.coefficient_comm 0 2]
    exact round20
  · intro m hO hI
    have hq : RawBoundaryIncidence.q = Assembly.q := by
      norm_num [RawBoundaryIncidence.q, Assembly.q]
    simpa [RawBoundaryCases.raw2, raw2, hq] using
      RawBoundaryCases.markedKernel_bound02 m hO hI

theorem boundary_t30 (f : ProfileSpace.State) :
    ‖component 3 (boundaryLayer (component 0 f))‖ ≤
      Assembly.t 2 * ‖component 0 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 3 0 raw3 _
    raw3_nonnegative ?_ ?_ f
  · exact round30
  · intro m hO hI
    simpa [RawBoundaryCases.raw3, raw3] using
      RawBoundaryCases.markedKernel_bound30 m hO hI

theorem boundary_t03 (f : ProfileSpace.State) :
    ‖component 0 (boundaryLayer (component 3 f))‖ ≤
      Assembly.t 2 * ‖component 3 f‖ := by
  apply RawBoundaryDegree.boundary_of_rounding 0 3 raw3 _
    raw3_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 0 3 raw3 ≤ Assembly.t 2
    rw [ResidualMatrix.coefficient_comm 0 3]
    exact round30
  · intro m hO hI
    simpa [RawBoundaryCases.raw3, raw3] using
      RawBoundaryCases.markedKernel_bound03 m hO hI

/-- All sixteen raw residual blocks, including the contraction-only region. -/
theorem boundary_C (i j : Fin 4) (f : ProfileSpace.State) :
    ‖component i.succ (boundaryLayer (component j.succ f))‖ ≤
      Assembly.C i j * ‖component j.succ f‖ := by
  fin_cases i <;> fin_cases j
  · exact boundary_C11 f
  · exact boundary_C12 f
  · exact boundary_C13 f
  · exact BoundaryContraction.raw_C_unit 0 3 (by norm_num) f
  · exact boundary_C21 f
  · exact boundary_C22 f
  · exact BoundaryContraction.raw_C_unit 1 2 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 1 3 (by norm_num) f
  · exact boundary_C31 f
  · exact BoundaryContraction.raw_C_unit 2 1 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 2 2 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 2 3 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 3 0 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 3 1 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 3 2 (by norm_num) f
  · exact BoundaryContraction.raw_C_unit 3 3 (by norm_num) f

theorem boundary_t10 (f : ProfileSpace.State) :
    ‖component 1 (boundaryLayer (component 0 f))‖ ≤
      Assembly.t 0 * ‖component 0 f‖ := by
  change ‖component 1 (WithLp.toLp 2
    (GroupedRecurrence.Pi (fun x => component 0 f x)))‖ ≤ _
  rw [BoundaryZeros.component_Pi_one_zero]
  norm_num [Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem boundary_t01 (f : ProfileSpace.State) :
    ‖component 0 (boundaryLayer (component 1 f))‖ ≤
      Assembly.t 0 * ‖component 1 f‖ := by
  change ‖component 0 (WithLp.toLp 2
    (GroupedRecurrence.Pi (fun x => component 1 f x)))‖ ≤ _
  rw [BoundaryZeros.component_Pi_zero_one]
  norm_num [Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

/-- Direct physical estimates from activity into all residual degrees. -/
theorem boundary_t_from_activity (i : Fin 4) (f : ProfileSpace.State) :
    ‖component i.succ (boundaryLayer (component 0 f))‖ ≤
      Assembly.t i * ‖component 0 f‖ := by
  fin_cases i
  · exact boundary_t10 f
  · exact boundary_t20 f
  · exact boundary_t30 f
  · exact BoundaryContraction.raw_four_activity f

/-- Direct physical estimates from all residual degrees into activity. -/
theorem boundary_t_to_activity (i : Fin 4) (f : ProfileSpace.State) :
    ‖component 0 (boundaryLayer (component i.succ f))‖ ≤
      Assembly.t i * ‖component i.succ f‖ := by
  fin_cases i
  · exact boundary_t01 f
  · exact boundary_t02 f
  · exact boundary_t03 f
  · exact BoundaryContraction.raw_activity_four f

end AESPaper.RawBoundaryTable
