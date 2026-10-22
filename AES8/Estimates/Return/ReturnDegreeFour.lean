/- Module role: Selected concrete high-return estimates.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Transfer.LowTransfer
import AESConcrete.FirstHighReturn

/-!
# The degree-four source and target high-return cell

This file treats only return cell `(13,13)`.  The intermediate high part is
expanded into coordinates 11, 12 and 13.  Its two outer degree-three legs use
the admitted all-step caps, and the source-13 legs use the existing degree
damping bounds.  The `(13,13)` leg uses the four-residual cap in both steps.
Centering and the actual intermediate high projection remain in every term.

The scalar comparison is against the authoritative `M` basis coefficient;
no old return-table cap or assumed profile recurrence is used.  Other return
cells and the first high remainder remain separate obligations.  Constructive
proof work only; no attacks or predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnDegreeFour
open AESMixing AESMixing.AES AESConcrete
open AES8.SupportProfile
open AES8.TransferAssembly (centeredStep highReturn physicalCoeff returnCoeff)

local notation "ρ" => (21 / 131072 : ℝ)

private theorem old_step_cap (i j : Fin 14) :
    ‖LegacyTransfer.euclideanBlock i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  exact AllStepCaps.physical_step_cap i j

private theorem step_eleven_thirteen_cap :
    ‖LegacyTransfer.euclideanBlock 11 13‖ ≤ ρ ^ 3 := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  have h := FirstHighReturn.system_step_eleven_thirteen_norm
  rw [PhysicalProjectionSystem.step_eq_physical] at h
  exact h

private theorem step_twelve_thirteen_cap :
    ‖LegacyTransfer.euclideanBlock 12 13‖ ≤ ρ ^ 3 := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  have h := FirstHighReturn.system_step_twelve_thirteen_norm
  rw [PhysicalProjectionSystem.step_eq_physical] at h
  exact h

private theorem step_thirteen_thirteen_cap :
    ‖LegacyTransfer.euclideanBlock 13 13‖ ≤ ρ ^ 4 := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  have h := FirstHighReturn.system_step_thirteen_thirteen_norm
  rw [PhysicalProjectionSystem.step_eq_physical] at h
  exact h

/-- Exact three-term high return on arbitrary joint real input. -/
theorem highReturn_eq_three (f : WordState → ℝ) :
    highReturn f =
      centeredStep (component (centeredStep f) 11) +
      centeredStep (component (centeredStep f) 12) +
      centeredStep (component (centeredStep f) 13) := by
  unfold highReturn SupportEvolution.highPart
  rw [TransferAssembly.centeredStep_sum]
  funext x
  simp [Fin.sum_univ_succ, add_assoc]

private theorem two_steps_profile_le (f : WordState → ℝ) (i k j : Fin 14)
    {a b : ℝ} (ha : ‖LegacyTransfer.euclideanBlock i k‖ ≤ a)
    (hb : ‖LegacyTransfer.euclideanBlock k j‖ ≤ b) :
    profile (centeredStep (component (centeredStep (component f j)) k)) i ≤
      (a * b) * profile f j := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  calc
    profile (centeredStep (component (centeredStep (component f j)) k)) i ≤
        a * profile (centeredStep (component f j)) k :=
      LegacyTransfer.profile_le_of_operator_cap (centeredStep (component f j)) i k ha
    _ ≤ a * (b * profile f j) :=
      mul_le_mul_of_nonneg_left (LegacyTransfer.profile_le_of_operator_cap f k j hb) ha0
    _ = (a * b) * profile f j := by ring

/-- Analytic majorant from the three actual centered return terms. -/
theorem return_thirteen_majorant (f : WordState → ℝ) :
    profile (highReturn (component f 13)) 13 ≤
      (AESRound.Terminal.lambda *
          (AESRound.Certificate.L 13 11 + AESRound.Certificate.L 13 12) * ρ ^ 3 +
        ρ ^ 8) * profile f 13 := by
  have h11 := two_steps_profile_le f 13 11 13
    (old_step_cap 13 11) step_eleven_thirteen_cap
  have h12 := two_steps_profile_le f 13 12 13
    (old_step_cap 13 12) step_twelve_thirteen_cap
  have h13 := two_steps_profile_le f 13 13 13
    step_thirteen_thirteen_cap step_thirteen_thirteen_cap
  rw [highReturn_eq_three]
  calc
    profile
        (centeredStep (component (centeredStep (component f 13)) 11) +
          centeredStep (component (centeredStep (component f 13)) 12) +
          centeredStep (component (centeredStep (component f 13)) 13)) 13 ≤
        profile
          (centeredStep (component (centeredStep (component f 13)) 11) +
            centeredStep (component (centeredStep (component f 13)) 12)) 13 +
          profile (centeredStep (component (centeredStep (component f 13)) 13)) 13 :=
      TransferAssembly.profile_add_le _ _ 13
    _ ≤
        (profile (centeredStep (component (centeredStep (component f 13)) 11)) 13 +
          profile (centeredStep (component (centeredStep (component f 13)) 12)) 13) +
          profile (centeredStep (component (centeredStep (component f 13)) 13)) 13 :=
      add_le_add (TransferAssembly.profile_add_le _ _ 13) le_rfl
    _ ≤
        ((AESRound.Terminal.lambda * AESRound.Certificate.L 13 11) * ρ ^ 3) *
            profile f 13 +
          ((AESRound.Terminal.lambda * AESRound.Certificate.L 13 12) * ρ ^ 3) *
            profile f 13 +
          (ρ ^ 4 * ρ ^ 4) * profile f 13 :=
      add_le_add (add_le_add h11 h12) h13
    _ =
        (AESRound.Terminal.lambda *
            (AESRound.Certificate.L 13 11 + AESRound.Certificate.L 13 12) * ρ ^ 3 +
          ρ ^ 8) * profile f 13 := by ring

/-- Remove the finite basis sum before simplifying any concrete indices. -/
theorem allSum_basis (j : Fin 14) : allSum (TransferAssembly.basis j) = 1 := by
  simp [allSum, TransferAssembly.basis]

-- This comparison uses only the existing M(13,13) basis coefficient; the
-- nine low-matrix enlargements do not enter this return-cell arithmetic.
/-- Exact comparison in physical units; the equal diagonal entries cancel. -/
theorem return_thirteen_scalar_le :
    AESRound.Terminal.lambda *
        (AESRound.Certificate.L 13 11 + AESRound.Certificate.L 13 12) * ρ ^ 3 +
      ρ ^ 8 ≤ physicalCoeff 2 13 13 (returnCoeff 13 13) := by
  simp only [TransferAssembly.physicalCoeff, TransferAssembly.returnCoeff, AES8.M, allSum_basis]
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L,
    TransferAssembly.physicalCoeff, TransferAssembly.returnCoeff,
    TransferAssembly.basis, AES8.M, M0, allSum, omega41, d, vec14_apply,
    Fin.sum_univ_succ, Fin.ext_iff]

/-- The `(13,13)` high field of `TransferAssembly.PhysicalCaps`, with no estimate premise. -/
theorem high_profile_cap (f : WordState → ℝ) :
    profile (highReturn (component f 13)) 13 ≤
      physicalCoeff 2 13 13 (returnCoeff 13 13) * profile f 13 :=
  (return_thirteen_majorant f).trans
    (mul_le_mul_of_nonneg_right return_thirteen_scalar_le (profile_nonneg f 13))

end AES8.ReturnDegreeFour
