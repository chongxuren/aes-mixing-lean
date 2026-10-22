/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ReturnCrossMiddleTen

/-! Actual counting-norm wrappers for the three cross middle branches.
 -/
set_option autoImplicit false
noncomputable section

namespace AES8.ReturnCrossMiddleActualL2
open AESMixing AESMixing.AES
open AES8.ProjectedGraph AES8.ZeroOutsideProjection AES8.MarkedZeroOverlap
open AES8.ReturnCrossMiddle AES8.ReturnCrossMiddleTen

theorem actual_zero_one_l2 (r c z : Fin 4) (f : RightDomain c z true → ℝ) :
    l2 (action (actualKernel r c z false true) f) ≤ SharpWordNorm.rho ^ 3 * l2 f :=
  zero_one_l2 r c z _ SharpWordNorm.rho (by norm_num [SharpWordNorm.rho])
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

theorem actual_eleven_l2 (r c z : Fin 4) (f : RightDomain c z true → ℝ) :
    l2 (action (actualKernel r c z true true) f) ≤ SharpWordNorm.rho ^ 3 * l2 f :=
  eleven_l2 r c z _ SharpWordNorm.rho (by norm_num [SharpWordNorm.rho])
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

theorem actual_one_zero_l2 (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (f : RightDomain c z false → ℝ) :
    l2 (action (actualKernel r c z true false) f) ≤
      (SharpWordNorm.rho ^ 2 * Real.sqrt OneSourceEventMoment.columnCap) * l2 f :=
  one_zero_l2 r c z s _ OneSourceEventMoment.columnCap SharpWordNorm.rho
    (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
    (by norm_num [SharpWordNorm.rho])
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_column_le f

end AES8.ReturnCrossMiddleActualL2
