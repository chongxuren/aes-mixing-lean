import AESConcrete.FirstHighReturn
import AESConcrete.MDSGraphFirstCap
import AESConcrete.NonzeroUniformGraphCap
import AESConcrete.DirectIncidenceStepCaps
import AESConcrete.UniformGraphScalar
import AESConcrete.ThreeResidualPlaneStepCaps

/-!
# Return cap (13,11)

The scalar comparison and actual operator composition have separate roles
below. This file uses the individual (11,11) step cap from
ThreeResidualPlaneStepCaps. Return13_12 is not a dependency of this file. No
desired source hypothesis is substituted, and this return cap alone does not
establish the full AES theorem.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section

namespace AESConcrete.Return13_11
open AESConcrete.PhysicalProjectionSystem (system)
open AESConcrete.UniformGraphScalar (rho)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L J)

set_option maxRecDepth 100000

/-- The six step caps give this scalar majorant in physical norm units. -/
def majorant : ℝ :=
  (lambda * L 13 11) * (lambda * L 11 11) +
  (lambda * L 13 12) * (lambda * L 12 11) +
  rho ^ 4 * (lambda * L 13 11)

/-- The unchanged frozen return target, with its required lambda squared. -/
def target : ℝ := lambda ^ 2 * J 13 11

section ScalarComparison

-- Editorial dependency: the positive margin is extremely small. Preserve the
-- exact frozen entries and this slack identity; decimal rounding is inadequate.
-- The preparation record gives the manual cleared-denominator calculation.
--
theorem return_scalar_slack :
    target - majorant =
      (177737519985092391927808 : ℝ) /
        ((2 : ℝ) ^ 96 * 500000000000000 * (10 : ℝ) ^ 25) := by
  norm_num [target, majorant, lambda, L, J, AESConcrete.UniformGraphScalar.rho]

/-- Scalar comparison only; the operator argument is supplied separately. -/
theorem return_scalar_strict : majorant < target := by
  apply sub_pos.mp
  rw [return_scalar_slack]
  positivity

theorem return_scalar_le : majorant ≤ target := le_of_lt return_scalar_strict

end ScalarComparison

section ActualSystem

-- User scope: retain the actual FirstHighReturn high indices 11,12,13.
-- The only new analytic source dependency is the pending (11,11) plane cap;
-- do not replace it by an assumed desired return or composition bound.
theorem system_return_bound : ‖system.ret 13 11‖ ≤ majorant := by
  have h13 : ‖system.step 13 13‖ ≤ rho ^ 4 := by
    simpa only [AESConcrete.UniformGraphScalar.rho] using
      FirstHighReturn.system_step_thirteen_thirteen_norm
  have h := FirstHighReturn.norm_three_compositions_le
    (system.step 13 11) (system.step 13 12) (system.step 13 13)
    (system.step 11 11) (system.step 12 11) (system.step 13 11)
    (lambda * L 13 11) (lambda * L 13 12) (rho ^ 4)
    (lambda * L 11 11) (lambda * L 12 11) (lambda * L 13 11)
    MDSGraphFirstCap.system_thirteen_eleven_step_cap
    NonzeroUniformGraphCap.system_thirteen_twelve_step_cap h13
    ThreeResidualPlaneStepCaps.system_11_11_step_cap
    (DirectIncidenceStepCaps.system_step_cap 12 11 (by decide))
    MDSGraphFirstCap.system_thirteen_eleven_step_cap
  rw [← FirstHighReturn.system_ret_eq_three_steps 13 11] at h
  exact h

theorem system_return_strict :
    ‖system.ret 13 11‖ < lambda ^ 2 * J 13 11 :=
  system_return_bound.trans_lt return_scalar_strict

/--
Actual-system cap; the step-cap dependency is explicit in the imports, rather
than an extra desired analytic premise.
-/
theorem system_return_cap :
    ‖system.ret 13 11‖ ≤ lambda ^ 2 * J 13 11 :=
  le_of_lt system_return_strict

end ActualSystem
end AESConcrete.Return13_11
