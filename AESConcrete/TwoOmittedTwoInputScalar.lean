import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
Lemmas for (10,10). This module supplies scalar inequalities only. The target
is C=(4q*rho*eta+8rho^2)^2/D^4 and the physical factor is36. Constructive
fixed AES10/14/16 only.
No desired-bound premise is assumed.
-/
noncomputable section
namespace AESConcrete.TwoOmittedTwoInputScalar
open AESConcrete.UniformGraphScalar (rho kappa)
open AESConcrete.ActivityCodeScalar (q s q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def columnNorm : ℝ := 19 / (52 * s)
def fullRawNorm : ℝ := q * rho * columnNorm
def eventRawNorm : ℝ := rho ^ 2
def inputNorm : ℝ := 2 * fullRawNorm + eventRawNorm
def outputSingleNorm : ℝ := fullRawNorm + 3 * eventRawNorm
def numerator : ℝ := 4 * fullRawNorm + 8 * eventRawNorm
def C : ℝ := numerator ^ 2 / (q - 1) ^ 4

theorem fullRawNorm_nonneg : 0 ≤ fullRawNorm := by
  norm_num [fullRawNorm, columnNorm, rho, q, s]
theorem eventRawNorm_nonneg : 0 ≤ eventRawNorm := sq_nonneg _
theorem inputNorm_nonneg : 0 ≤ inputNorm := by
  exact add_nonneg (mul_nonneg (by norm_num) fullRawNorm_nonneg) eventRawNorm_nonneg
theorem outputSingleNorm_nonneg : 0 ≤ outputSingleNorm := by
  exact add_nonneg fullRawNorm_nonneg (mul_nonneg (by norm_num) eventRawNorm_nonneg)

theorem kappa_le_columnNorm_sq : kappa ≤ columnNorm ^ 2 := by
  norm_num [kappa, columnNorm, s]

theorem full_energy_coefficient_le : q ^ 2 * rho ^ 2 * kappa ≤ fullRawNorm ^ 2 := by
  calc
    _ ≤ q ^ 2 * rho ^ 2 * columnNorm ^ 2 := mul_le_mul_of_nonneg_left
      kappa_le_columnNorm_sq (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by unfold fullRawNorm; ring

theorem event_energy_coefficient_eq : rho ^ 4 = eventRawNorm ^ 2 := by
  unfold eventRawNorm
  ring

theorem input_coefficient_eq : 0 + fullRawNorm + fullRawNorm + eventRawNorm = inputNorm := by
  unfold inputNorm
  ring

theorem outer_coefficient_eq :
    ((inputNorm / (q - 1) + outputSingleNorm / (q - 1) +
      outputSingleNorm / (q - 1) + eventRawNorm / (q - 1)) ^ 2 / (q - 1) ^ 2) = C := by
  have hd : q - 1 ≠ 0 := ne_of_gt q_sub_one_pos
  unfold inputNorm outputSingleNorm C numerator
  field_simp [hd]
  <;> ring

theorem C_nonneg : 0 ≤ C := div_nonneg (sq_nonneg _) (pow_nonneg q_sub_one_pos.le _)

theorem numerator_exact : numerator = (399 : ℝ) / 26 + 882 / q := by
  norm_num [numerator, fullRawNorm, columnNorm, eventRawNorm, rho, q, s]

theorem certificate_10_10_entry : L (10 : Fin 14) (10 : Fin 14) =
    (429488723112867 : ℝ) / 30822753906250000000 := rfl

theorem certificate_product_pos : 0 < lambda * L 10 10 := by
  rw [certificate_10_10_entry]
  norm_num [AESRound.Terminal.lambda]

/-- Common exact norm threshold from the reviewed handwritten route. -/
theorem scaled_norm_lt_threshold : q ^ 2 * (6 * numerator / (q - 1) ^ 2) < (921 : ℝ) / 10 := by
  norm_num [numerator, fullRawNorm, columnNorm, eventRawNorm, rho, q, s]

theorem threshold_lt_scaled_certificate : (921 : ℝ) / 10 < q ^ 2 * (lambda * L 10 10) := by
  rw [certificate_10_10_entry]
  norm_num [AESRound.Terminal.lambda, q]

theorem certificate_strict_bound : 36 * C < (lambda * L 10 10) ^ 2 := by
  rw [certificate_10_10_entry]
  norm_num [C, numerator, fullRawNorm, columnNorm, eventRawNorm, rho, q, s, AESRound.Terminal.lambda]

theorem certificate_bound : 0 ≤ lambda * L 10 10 ∧ 36 * C ≤ (lambda * L 10 10) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩
end AESConcrete.TwoOmittedTwoInputScalar
