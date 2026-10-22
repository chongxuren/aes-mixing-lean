/- Module role: Concrete transfer caps and their comparison to the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.LegacyTransfer
import AES8.Estimates.Word.SharpWordNorm
import AESConcrete.DegreeResidualStep

/-!
# A sharper actual centered step from type 13 to type 12

The generic degree-damping theorem is instantiated with the new actual
word-residual energy theorem, at `SharpWordNorm.rho`. The target refinement
has whole-word degree three, and the input refinement has degree four.
Both exact support projections, the actual input permutation, and the
centered kernel remain in the operator being bounded.

Inputs are arbitrary signed joint real functions on the full word-state
space. This supplies only the `(12,13)` step leg and its profile transport;
first-high assembly, return cells, and the complete theorem are separate.
Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

noncomputable section
open scoped BigOperators

namespace AES8.SharpDegreeStep
open AESMixing AESMixing.AES AESConcrete

/-- The forward actual word channel receives the new residual-energy bound. -/
theorem word_superbox_residual_energy (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix AES.wordSuperboxKernel 0) f x ^ 2) ≤
      SharpWordNorm.rho ^ 2 * ∑ x, f x ^ 2 := by
  simpa only [WordOrientationClosure.ordinary_word_kernel] using
    SharpWordNorm.residual_energy .ordinary .ordinary false f

-- The finite type order is intentional: 12 = (3,4), 13 = (4,4).
-- The generic theorem contracts both refined projections and cancels the
-- global uniform term using positive output degree; no old numerical cap is used.
theorem physical_twelve_thirteen_energy (f : WordState → ℝ) :
    (∑ y, action (LegacyTransfer.physicalBlock 12 13) f y ^ 2) ≤
      (SharpWordNorm.rho ^ (3 : ℕ)) ^ 2 * ∑ x, f x ^ 2 := by
  exact DegreeResidualStep.refined_centered_energy AES.wordSuperboxKernel
    (0 : AES.Word) SupportProfile.word_card_gt_one AES.word_superbox_pointed
    SharpWordNorm.rho word_superbox_residual_energy
    3 4 4 4 (by decide) WordCrossZero.wordMixAddEquiv.toEquiv f

/-- Sharper bound for the exact projected centered operator, with no normalization loss. -/
theorem twelve_thirteen_operator_cap :
    ‖LegacyTransfer.euclideanBlock 12 13‖ ≤ SharpWordNorm.rho ^ (3 : ℕ) := by
  change ‖kernelOperator (LegacyTransfer.physicalBlock 12 13)‖ ≤ _
  exact kernelOperator_norm_le _
    (pow_nonneg (by norm_num [SharpWordNorm.rho]) 3)
    physical_twelve_thirteen_energy

/-- Transport the same cap to the arbitrary-input counting profile. -/
theorem twelve_thirteen_profile_cap (f : WordState → ℝ) :
    SupportProfile.profile
      (TransferAssembly.centeredStep (SupportProfile.component f 13)) 12 ≤
      SharpWordNorm.rho ^ (3 : ℕ) * SupportProfile.profile f 13 :=
  LegacyTransfer.profile_le_of_operator_cap f 12 13 twelve_thirteen_operator_cap

end AES8.SharpDegreeStep
