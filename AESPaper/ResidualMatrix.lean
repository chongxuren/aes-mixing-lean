import AESPaper.WordDegreeResidual
import AESPaper.WordResidualReverse

/-!
# Complete residual-to-residual S table for the actual sandwich
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace AESPaper.ResidualMatrix
open AESPaper.ProfileSpace

/-- Only the scalar position/frame coefficient is symmetric. -/
theorem coefficient_comm (i j : ℕ) (raw : ℝ) :
    ResidualRounding.coefficient i j raw = ResidualRounding.coefficient j i raw := by
  unfold ResidualRounding.coefficient
  rw [mul_comm (Nat.choose 4 i : ℝ) (Nat.choose 4 j : ℝ)]
  ring

/-- Exact symmetry of the printed numerical table, not of the AES operator. -/
theorem S_symmetric (i j : Fin 4) : Assembly.S i j = Assembly.S j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Assembly.S, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

/-- Actual reverse degree bound, using its direct physical marked estimate. -/
theorem sandwich_S21 (f : ProfileSpace.State) :
    ‖component 2 (BoundaryContraction.sandwich (component 1 f))‖ ≤
      (Assembly.S 1 0 / Assembly.q ^ 2) * ‖component 1 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 2 1 ResidualRounding.raw12 _
    ResidualRounding.raw12_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 2 1 ResidualRounding.raw12 ≤
      Assembly.S 1 0 / Assembly.q ^ 2
    rw [coefficient_comm 2 1, S_symmetric 1 0]
    exact ResidualRounding.round12
  · intro m hO hI
    simpa [ResidualRounding.raw12] using WordResidualReverse.markedKernel_bound21 m hO hI

/-- Actual reverse degree bound, using its direct physical marked estimate. -/
theorem sandwich_S31 (f : ProfileSpace.State) :
    ‖component 3 (BoundaryContraction.sandwich (component 1 f))‖ ≤
      (Assembly.S 2 0 / Assembly.q ^ 2) * ‖component 1 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 3 1 ResidualRounding.raw13 _
    ResidualRounding.raw13_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 3 1 ResidualRounding.raw13 ≤
      Assembly.S 2 0 / Assembly.q ^ 2
    rw [coefficient_comm 3 1, S_symmetric 2 0]
    exact ResidualRounding.round13
  · intro m hO hI
    simpa [ResidualRounding.raw13] using WordResidualReverse.markedKernel_bound31 m hO hI

/-- Actual reverse degree bound, using its direct physical marked estimate. -/
theorem sandwich_S41 (f : ProfileSpace.State) :
    ‖component 4 (BoundaryContraction.sandwich (component 1 f))‖ ≤
      (Assembly.S 3 0 / Assembly.q ^ 2) * ‖component 1 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 4 1 ResidualRounding.raw14 _
    ResidualRounding.raw14_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 4 1 ResidualRounding.raw14 ≤
      Assembly.S 3 0 / Assembly.q ^ 2
    rw [coefficient_comm 4 1, S_symmetric 3 0]
    exact ResidualRounding.round14
  · intro m hO hI
    simpa [ResidualRounding.raw14] using WordResidualReverse.markedKernel_bound41 m hO hI

/-- Actual reverse degree bound, using its direct physical marked estimate. -/
theorem sandwich_S32 (f : ProfileSpace.State) :
    ‖component 3 (BoundaryContraction.sandwich (component 2 f))‖ ≤
      (Assembly.S 2 1 / Assembly.q ^ 2) * ‖component 2 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 3 2 ResidualRounding.raw23 _
    ResidualRounding.raw23_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 3 2 ResidualRounding.raw23 ≤
      Assembly.S 2 1 / Assembly.q ^ 2
    rw [coefficient_comm 3 2, S_symmetric 2 1]
    exact ResidualRounding.round23
  · intro m hO hI
    simpa [ResidualRounding.raw23] using WordResidualReverse.markedKernel_bound32 m hO hI

/-- Actual reverse degree bound, using its direct physical marked estimate. -/
theorem sandwich_S42 (f : ProfileSpace.State) :
    ‖component 4 (BoundaryContraction.sandwich (component 2 f))‖ ≤
      (Assembly.S 3 1 / Assembly.q ^ 2) * ‖component 2 f‖ := by
  apply WordDegreeResidual.sandwich_of_rounding 4 2 ResidualRounding.raw24 _
    ResidualRounding.raw24_nonnegative ?_ ?_ f
  · change ResidualRounding.coefficient 4 2 ResidualRounding.raw24 ≤
      Assembly.S 3 1 / Assembly.q ^ 2
    rw [coefficient_comm 4 2, S_symmetric 3 1]
    exact ResidualRounding.round24
  · intro m hO hI
    simpa [ResidualRounding.raw24] using WordResidualReverse.markedKernel_bound42 m hO hI

/-- All sixteen entries of the printed residual table bound the actual
sandwich, with no unproved block, centering or independence premise. -/
theorem sandwich_S (i j : Fin 4) (f : ProfileSpace.State) :
    ‖component i.succ (BoundaryContraction.sandwich (component j.succ f))‖ ≤
      (Assembly.S i j / Assembly.q ^ 2) * ‖component j.succ f‖ := by
  fin_cases i <;> fin_cases j
  · exact WordDegreeResidual.sandwich_S11 f
  · exact WordDegreeResidual.sandwich_S12 f
  · exact WordDegreeResidual.sandwich_S13 f
  · exact WordDegreeResidual.sandwich_S14 f
  · exact sandwich_S21 f
  · exact WordDegreeResidual.sandwich_S22 f
  · exact WordDegreeResidual.sandwich_S23 f
  · exact WordDegreeResidual.sandwich_S24 f
  · exact sandwich_S31 f
  · exact sandwich_S32 f
  · exact WordDegreeResidual.sandwich_S33 f
  · exact BoundaryContraction.sandwich_S34 f
  · exact sandwich_S41 f
  · exact sandwich_S42 f
  · exact BoundaryContraction.sandwich_S43 f
  · exact BoundaryContraction.sandwich_S44 f

end AESPaper.ResidualMatrix
