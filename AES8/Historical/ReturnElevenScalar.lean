/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Return.ReturnDegreeFour
import Mathlib.Analysis.Real.Sqrt

/-!
# Scalar margin for the historical five-branch return-eleven bound

This module checks the numerical sum of five proposed branch constants against
the existing physical recurrence allowance. It supplies no operator bound;
all projected branch inequalities and their assembly remain separate obligations.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace AES8.ReturnElevenScalar
open AES8.TransferAssembly

def q : ℝ := 4294967296
def delta : ℝ := 2 / (15 * q)
def nu : ℝ := 52 / (5 * 65536)
def xi : ℝ := 1 / 65536
def eta : ℝ := q / (q - 1)
def assembled : ℝ :=
  16 * eta * (nu ^ 3 * delta * Real.sqrt delta +
    2 * xi ^ 2 * nu ^ 5 * Real.sqrt delta + xi ^ 2 * nu ^ 6) +
      4 * delta * nu ^ 5

theorem sqrt_delta_lt : Real.sqrt delta < 11 / (30 * 65536) := by
  have he := Real.sq_sqrt (show (0 : ℝ) ≤ delta by norm_num [delta, q])
  have hn := Real.sqrt_nonneg delta
  have hb : delta < (11 / (30 * 65536) : ℝ) ^ 2 := by norm_num [delta, q]
  have ht : (0 : ℝ) < 11 / (30 * 65536) := by norm_num
  nlinarith only [he, hn, hb, ht]

/-- A rational upper bound leaves a visible strict margin. -/
theorem assembled_lt : assembled < 882 / q ^ 3 := by
  have hp : (0 : ℝ) ≤ 16 * eta * (nu ^ 3 * delta + 2 * xi ^ 2 * nu ^ 5) := by
    norm_num [eta, nu, delta, xi, q]
  calc
    assembled = (16 * eta * (nu ^ 3 * delta + 2 * xi ^ 2 * nu ^ 5)) * Real.sqrt delta +
      (16 * eta * xi ^ 2 * nu ^ 6 + 4 * delta * nu ^ 5) := by unfold assembled; ring
    _ ≤ (16 * eta * (nu ^ 3 * delta + 2 * xi ^ 2 * nu ^ 5)) * (11 / (30 * 65536)) +
      (16 * eta * xi ^ 2 * nu ^ 6 + 4 * delta * nu ^ 5) :=
      by
        have h := mul_le_mul_of_nonneg_left sqrt_delta_lt.le hp
        linarith only [h]
    _ < 882 / q ^ 3 := by norm_num [eta, nu, delta, xi, q]

theorem allowance_eq :
    physicalCoeff 2 11 11 (returnCoeff 11 11) = (110842 / 125) / q ^ 3 := by
  simp only [physicalCoeff, returnCoeff, AES8.M, ReturnDegreeFour.allSum_basis]
  norm_num [basis, M0, omega41, d, vec14_apply, q, Fin.ext_iff]

theorem assembled_lt_allowance :
    assembled < physicalCoeff 2 11 11 (returnCoeff 11 11) := by
  rw [allowance_eq]
  exact assembled_lt.trans (by norm_num [q])

end AES8.ReturnElevenScalar
