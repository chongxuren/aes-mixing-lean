import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
Lemmas for (10,9). This module supplies scalar inequalities only. columnNorm
is eta = 19/(52s), a scalar upper bound for sqrt kappa. The raw full
coefficient retains BOTH q losses. The original input U supplies sqrt D; the
two omitted output U factors supply D. Full + four event norms produce
N=q*rho*eta+4*rho^2 and C=N^2/D^3. Physical factor 72 is separate.
Constructive fixed AES10/14/16 only.

No endpoint assumption is imposed.
-/

noncomputable section
namespace AESConcrete.OmittedPairOneInputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_sub_one_pos s_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

-- Editorial choice: the inherited 11/(30*s) column-norm envelope is too
-- coarse for this route. This finer rational envelope is an independent
-- scalar obligation; no new analytic resource is introduced.
def columnNorm : ℝ := 19 / (52 * s)
def fullRawNorm : ℝ := q * rho * columnNorm
def eventRawNorm : ℝ := rho ^ 2
def numerator : ℝ := fullRawNorm + 4 * eventRawNorm
def C : ℝ := numerator ^ 2 / (q - 1) ^ 3

theorem columnNorm_nonneg : 0 ≤ columnNorm := by
  norm_num [columnNorm, s]

theorem kappa_le_columnNorm_sq : kappa ≤ columnNorm ^ 2 := by
  norm_num [columnNorm, kappa, s]

theorem columnNorm_squared_margin : columnNorm ^ 2 - kappa = 7 / (40560 * s ^ 2) := by
  norm_num [columnNorm, kappa, s]

theorem fullRawNorm_nonneg : 0 ≤ fullRawNorm := by
  norm_num [fullRawNorm, columnNorm, rho, q, s]

theorem eventRawNorm_nonneg : 0 ≤ eventRawNorm := sq_nonneg _

theorem full_energy_coefficient_le :
    q ^ 2 * rho ^ 2 * kappa ≤ fullRawNorm ^ 2 := by
  calc
    q ^ 2 * rho ^ 2 * kappa ≤ q ^ 2 * rho ^ 2 * columnNorm ^ 2 :=
      mul_le_mul_of_nonneg_left kappa_le_columnNorm_sq
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = fullRawNorm ^ 2 := by unfold fullRawNorm; ring

theorem intersection_energy_coefficient_le :
    rho ^ 2 * kappa ≤ eventRawNorm ^ 2 := by
  norm_num [eventRawNorm, rho, kappa]

/-- The input-zero and singleton output-zero planes use the ordinary pair operator. -/
theorem single_energy_coefficient_eq : rho ^ 4 = eventRawNorm ^ 2 := by
  unfold eventRawNorm
  ring

def inputNorm : ℝ := fullRawNorm + eventRawNorm

theorem inputNorm_nonneg : 0 ≤ inputNorm :=
  add_nonneg fullRawNorm_nonneg eventRawNorm_nonneg

theorem input_norm_numerator :
    fullRawNorm + eventRawNorm = inputNorm := by
  unfold inputNorm
  ring

theorem split_coefficient_eq :
    (inputNorm + 3 * eventRawNorm) ^ 2 / (q - 1) ^ 3 = C := by
  unfold inputNorm C numerator
  ring

theorem four_event_numerator :
    fullRawNorm + eventRawNorm + eventRawNorm + eventRawNorm + eventRawNorm =
      numerator := by
  unfold numerator
  ring

theorem C_nonneg : 0 ≤ C :=
  div_nonneg (sq_nonneg _) (pow_nonneg q_sub_one_pos.le _)

theorem certificate_10_9_entry :
    L (10 : Fin 14) (9 : Fin 14) =
      (621966114212136 : ℝ) / 1926422119140625 := rfl

theorem certificate_product_pos : 0 < lambda * L 10 9 := by
  rw [certificate_10_9_entry]
  norm_num [AESRound.Terminal.lambda]

-- Twelve input support pieces and six orthogonal output energies give 72.
-- This file compares the fixed scalar only; it supplies no physical premise.
theorem columnNorm_le_rho : columnNorm ≤ rho := by
  norm_num [columnNorm, rho, s]

theorem numerator_exact : numerator = (399 : ℝ) / 104 + 441 / q := by
  norm_num [numerator, fullRawNorm, eventRawNorm, columnNorm, rho, q, s]

theorem numerator_lt_96_25 : numerator < (96 : ℝ) / 25 := by
  norm_num [numerator, fullRawNorm, eventRawNorm, columnNorm, rho, q, s]

/-- Exact positive margin of the rational envelope, not a numerical estimate. -/
theorem rational_envelope_margin :
    (lambda * L 10 9) ^ 2 * (q - 1) ^ 3 - 72 * ((96 : ℝ) / 25) ^ 2 =
      (5979238638296984549632182826796014598380780264985331 : ℝ) /
        3602879701896396800000000000000000000000000000000000 := by
  rw [certificate_10_9_entry]
  norm_num [AESRound.Terminal.lambda, q]

theorem certificate_strict_bound : 72 * C < (lambda * L 10 9) ^ 2 := by
  rw [certificate_10_9_entry]
  norm_num [C, numerator, fullRawNorm, eventRawNorm, columnNorm,
    rho, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 10 9 ∧ 72 * C ≤ (lambda * L 10 9) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.OmittedPairOneInputScalar
