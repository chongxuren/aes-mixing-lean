-- Source-only successor for job 15958825; signatures and physical model retained.
--
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar
import AESConcrete.WeightedResponse

/-!
# Exact scalar coefficient and unchanged certificate for (10,12)

In particular kappa<=eta^2 is directly proved here from 5408<=5415; it is not
imported from another scalar conclusion. Normalizers and rational arithmetic
are separate from all analytic estimates. Constructive fixed AES10/14/16.
-/

noncomputable section
namespace AESConcrete.TwoOmittedOneInputScalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

def D : ℝ := q - 1
def d : ℝ := Real.sqrt D
def eta : ℝ := 19 / (52 * s)
def fullRawNorm : ℝ := s * q * rho * eta
def inputZeroNorm : ℝ := s * rho ^ 2
def inputNorm : ℝ := (fullRawNorm + inputZeroNorm) / d
def singleNorm : ℝ := s * rho ^ 2 / d
def doubleNorm : ℝ := rho ^ 2 / d
def N : ℝ := s * q * rho * eta + (3 * s + 1) * rho ^ 2
def C : ℝ := N ^ 2 / D ^ 3

theorem D_pos : 0 < D := q_sub_one_pos
theorem d_pos : 0 < d := Real.sqrt_pos.2 D_pos
theorem d_sq : d ^ 2 = D := Real.sq_sqrt D_pos.le
theorem eta_nonneg : 0 ≤ eta := div_nonneg (by norm_num) (mul_nonneg (by norm_num) s_pos.le)

theorem kappa_formula : kappa = 2 / (15 * s ^ 2) := by
  norm_num [kappa, s]

theorem kappa_le_eta_sq : kappa ≤ eta ^ 2 := by
  -- All three constants are fixed rationals. Direct exact normalization
  -- avoids convert-generated relation goals and ring on an inequality.
  norm_num [kappa, eta, s]

theorem sqrt_kappa_le_eta : Real.sqrt kappa ≤ eta := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) eta_nonneg).mp
  rw [Real.sq_sqrt kappa_nonneg]
  exact kappa_le_eta_sq

theorem fullRawNorm_nonneg : 0 ≤ fullRawNorm := by
  unfold fullRawNorm
  exact mul_nonneg (mul_nonneg (mul_nonneg s_pos.le q_pos.le) rho_nonneg) eta_nonneg

theorem inputZeroNorm_nonneg : 0 ≤ inputZeroNorm := mul_nonneg s_pos.le (sq_nonneg rho)
theorem inputNorm_nonneg : 0 ≤ inputNorm := div_nonneg (add_nonneg fullRawNorm_nonneg inputZeroNorm_nonneg) d_pos.le

theorem singleNorm_nonneg : 0 ≤ singleNorm := div_nonneg (mul_nonneg s_pos.le (sq_nonneg rho)) d_pos.le
theorem doubleNorm_nonneg : 0 ≤ doubleNorm := div_nonneg (sq_nonneg rho) d_pos.le

theorem C_nonneg : 0 ≤ C := div_nonneg (sq_nonneg N) (pow_nonneg D_pos.le _)

theorem full_energy_coefficient_le : q ^ 3 * rho ^ 2 * kappa ≤ fullRawNorm ^ 2 := by
  calc
    _ ≤ q ^ 3 * rho ^ 2 * eta ^ 2 :=
      mul_le_mul_of_nonneg_left kappa_le_eta_sq
        (mul_nonneg (pow_nonneg q_pos.le _) (sq_nonneg rho))
    _ = _ := by
      unfold fullRawNorm
      simp only [mul_pow, s_sq]
      ring

theorem inputZeroNorm_sq : inputZeroNorm ^ 2 = q * rho ^ 4 := by
  unfold inputZeroNorm
  rw [mul_pow, s_sq]
  ring

theorem singleNorm_sq : singleNorm ^ 2 = q * rho ^ 4 / D := by
  unfold singleNorm
  rw [div_pow, mul_pow, s_sq, d_sq]
  ring

theorem doubleNorm_sq : doubleNorm ^ 2 = rho ^ 4 / D := by
  unfold doubleNorm
  rw [div_pow, d_sq]
  ring

theorem norm_sum : inputNorm + singleNorm + singleNorm + doubleNorm = N / d := by
  unfold inputNorm inputZeroNorm fullRawNorm singleNorm doubleNorm N
  ring

theorem combined_coefficient :
    ((inputNorm + singleNorm + singleNorm + doubleNorm) / D) ^ 2 = C := by
  rw [norm_sum, div_div, div_pow, mul_pow, d_sq]
  unfold C
  congr 1
  ring

theorem N_over_s : N / s = 399 / 104 + 441 * (3 * s + 1) / (4 * s ^ 3) := by
  norm_num [N, q, s, rho, eta]

theorem certificate_10_12_entry :
    L (10 : Fin 14) (12 : Fin 14) = (7530711418750692 : ℝ) / 616455078125 := rfl

theorem certificate_product_pos : 0 < lambda * L 10 12 := by
  rw [certificate_10_12_entry]
  norm_num [AESRound.Terminal.lambda]

/-- Exact rational form of the handwritten upper separation; no numerical sqrt. -/
theorem separator_energy : q ^ 2 * (24 * C) < (1881 / 100 : ℝ) ^ 2 := by
  norm_num [C, N, D, eta, rho, q, s]

theorem separator_lower : (1881 / 100 : ℝ) < q * lambda * L 10 12 := by
  rw [certificate_10_12_entry]
  norm_num [q, AESRound.Terminal.lambda]

theorem separator_sqrt : q * Real.sqrt (24 * C) < (1881 / 100 : ℝ) := by
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) C_nonneg)
  have hp := Real.sqrt_nonneg (24 * C)
  apply (sq_lt_sq₀ (mul_nonneg q_pos.le hp) (by norm_num : (0 : ℝ) ≤ 1881 / 100)).mp
  rw [mul_pow, hs]
  exact separator_energy

/-- Unchanged-certificate comparison for the exact coefficient proved analytically. -/
theorem certificate_strict_bound : 24 * C < (lambda * L 10 12) ^ 2 := by
  have hsep : q * Real.sqrt (24 * C) < q * (lambda * L 10 12) := by
    simpa only [mul_assoc] using lt_trans separator_sqrt separator_lower
  have hlt : Real.sqrt (24 * C) < lambda * L 10 12 := by
    -- Definition-only exposure of q preserves sqrt (24*C) as one atom.
    -- norm_num [q] also split that radical in the executed predecessor.
    change (4294967296 : ℝ) * Real.sqrt (24 * C) <
      (4294967296 : ℝ) * (lambda * L 10 12) at hsep
    linarith only [hsep]
  have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg (24 * C)) certificate_product_pos.le).mpr hlt
  rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) C_nonneg)] at hsq
  exact hsq

theorem certificate_bound :
    0 ≤ lambda * L 10 12 ∧ 24 * C ≤ (lambda * L 10 12) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.TwoOmittedOneInputScalar
