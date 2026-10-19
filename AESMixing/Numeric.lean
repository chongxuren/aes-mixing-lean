import AESMixing.MatrixEstimate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Exact finite arithmetic from Sections 4--6. The geometric comparison of
the actual AES operator with these matrices is a separate obligation. -/
noncomputable section
open scoped BigOperators Matrix
namespace AESMixing

def byteComparison : Fin 5 → Fin 5 → ℝ :=
  !![1/10400, 0, 7/500, 9/50, 1;
      0, 27/8000, 43/500, 1, 1;
      7/500, 43/500, 9/10, 1, 1;
      9/50, 1, 1, 1, 1;
      1, 1, 1, 1, 1]

def dampedComparison (i j : Fin 5) : ℝ :=
  (9 / 128 : ℝ) ^ (i.val + j.val) * byteComparison i j

def comparisonWitness : Fin 5 → ℝ := ![13, 3, 7, 6, 2]

theorem comparisonWitness_pos (i : Fin 5) : 0 < comparisonWitness i := by
  fin_cases i <;> norm_num [comparisonWitness]

theorem dampedComparison_nonneg (i j : Fin 5) : 0 ≤ dampedComparison i j := by
  fin_cases i <;> fin_cases j <;> norm_num [dampedComparison, byteComparison]

theorem dampedComparison_symmetric (i j : Fin 5) :
    dampedComparison i j = dampedComparison j i := by
  fin_cases i <;> fin_cases j <;> norm_num [dampedComparison, byteComparison]

theorem local_comparison_certificate (i : Fin 5) :
    (∑ j, dampedComparison i j * comparisonWitness j) <
      (11 / 65536 : ℝ) * comparisonWitness i := by
  fin_cases i <;> norm_num [dampedComparison, byteComparison,
    comparisonWitness, Fin.sum_univ_succ]

theorem local_comparison_energy (x : Fin 5 → ℝ) :
    (∑ i, (∑ j, dampedComparison i j * x j) ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ j, x j ^ 2 := by
  exact weighted_schur_energy dampedComparison comparisonWitness (11 / 65536)
    (by norm_num) dampedComparison_nonneg dampedComparison_symmetric
    comparisonWitness_pos (fun i => le_of_lt (local_comparison_certificate i)) x

theorem trace_calibration :
    (68 * (256 : ℝ)^2 + 264 * 256 + 68) / 255^6 +
      (((81 / 64 : ℝ) + 32 / 15)^8 - (32 / 15 : ℝ)^8 -
        8 * (81 / 64 : ℝ) * (32 / 15 : ℝ)^7) / 256^4 <
      1 / (2 : ℝ)^18 := by norm_num

theorem gram_moment_calibration :
    (11 / 65536 : ℝ)^2 * (1 / (2 : ℝ)^18) < 1 / (2 : ℝ)^43 := by norm_num

theorem coupling_calibration :
    (24 / (1 - 1 / (65536 : ℝ))^2 + 8 / (1 - 1 / (65536 : ℝ)) + 1) *
      (14 / (1 - 1 / (65536 : ℝ))^4) < 512 := by norm_num

theorem first_degree_calibration :
    4 * (13 + (2 : ℝ)^32 / ((2 : ℝ)^32 - 1)) < 60 := by norm_num

theorem shared_source_calibration :
    (11 * 128 * 400 * 3 : ℝ) / (2 : ℝ)^19 < 4 := by norm_num

theorem independent_source_calibration : (81 : ℝ) / 4096 < 1 := by norm_num

theorem smoothing_exponent :
    64 / ((2 : ℝ)^32)^5 = 1 / (2 : ℝ)^154 := by norm_num

theorem contraction_exponent :
    8 / ((2 : ℝ)^32)^2 = 1 / (2 : ℝ)^61 := by norm_num

end AESMixing
