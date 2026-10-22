import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Scalar candidate for the actual omitted-output pair-input route

Source authoring only: no compilation, independent review or acceptance.
This file proves no response estimate and no physical operator bound.
The proposed full raw coefficient is q^2*rho^2*kappa, obtained from a
noninjective retained pushforward followed by one-free/one-dependent
Fourier graph energy. The stronger proposed q*rho^4 coefficient is NOT used.
The two singleton input-zero events, the double event and the normalized
extra-output-zero response must separately be proved against the SAME
arbitrary signed JOINT residual-pair h, including h(0,0).

Fixed constructive AES10/14/16; independent uniform retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.
No attacks. No live source, manuscript, inventory or admission edits.
-/

noncomputable section
namespace AESConcrete.OmittedUniformTwoInputPairScalar
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

/-- The two singleton input events use the ordinary two-coordinate operator. -/
theorem single_energy_coefficient_eq : rho ^ 4 = eventRawNorm ^ 2 := by
  unfold eventRawNorm
  ring

def inputNorm : ℝ := fullRawNorm + 3 * eventRawNorm

theorem inputNorm_nonneg : 0 ≤ inputNorm :=
  add_nonneg fullRawNorm_nonneg (mul_nonneg (by norm_num) eventRawNorm_nonneg)

theorem input_norm_numerator :
    fullRawNorm + eventRawNorm + eventRawNorm + eventRawNorm = inputNorm := by
  unfold inputNorm
  ring

theorem split_coefficient_eq :
    (inputNorm + eventRawNorm) ^ 2 / (q - 1) ^ 3 = C := by
  unfold inputNorm C numerator
  ring

theorem four_event_numerator :
    fullRawNorm + eventRawNorm + eventRawNorm + eventRawNorm + eventRawNorm =
      numerator := by
  unfold numerator
  ring

theorem C_nonneg : 0 ≤ C :=
  div_nonneg (sq_nonneg _) (pow_nonneg q_sub_one_pos.le _)

theorem certificate_9_10_entry :
    L (9 : Fin 14) (10 : Fin 14) =
      (621966114212136 : ℝ) / 1926422119140625 := rfl

theorem certificate_product_pos : 0 < lambda * L 9 10 := by
  rw [certificate_9_10_entry]
  norm_num [AESRound.Terminal.lambda]

-- Six input support pieces and twelve orthogonal output energies are a
-- separate physical-aggregation obligation. This draft is unexecuted.
theorem certificate_strict_bound : 72 * C < (lambda * L 9 10) ^ 2 := by
  rw [certificate_9_10_entry]
  norm_num [C, numerator, fullRawNorm, eventRawNorm, columnNorm,
    rho, q, s, AESRound.Terminal.lambda]

theorem certificate_bound :
    0 ≤ lambda * L 9 10 ∧ 72 * C ≤ (lambda * L 9 10) ^ 2 :=
  ⟨certificate_product_pos.le, certificate_strict_bound.le⟩

end AESConcrete.OmittedUniformTwoInputPairScalar
