import AESConcrete.HighReturnRow
import AESConcrete.WeightedResidualLineStepCaps
import AESConcrete.TwoOutputThreeUniformStepCaps
import AESConcrete.WeightedOutputLineStepCaps
import AESConcrete.WeightedThreeOutputStepCaps
import AESConcrete.CoupledTripleStepCaps
import AESConcrete.TwoUniformThreeOutputStepCaps
import AESConcrete.ThreeUniformThreeOutputStepCaps
import AESConcrete.OmittedUniformTwoOutputStepCaps
import AESConcrete.OmittedUniformTwoInputStepCaps
import AESConcrete.OmittedUniformTwoInputPairStepCaps
import AESConcrete.TwoOmittedOutputStepCaps
import AESConcrete.TwoOmittedThreeInputStepCaps
import AESConcrete.OmittedPairOneInputStepCaps
import AESConcrete.TwoOmittedTwoInputStepCaps
import AESConcrete.TwoOmittedOneInputStepCaps
import AESConcrete.PhysicalLowHigh

/-!
# Assembly of all actual physical step caps

The HighReturnRow import closure supplies the core step interfaces. The
supplemental cells are dispatched to their individual physical cap theorems.

The finite predicate only routes indices. Each quantitative bound is obtained
from its owning physical cap theorem, with every original physical factor,
signed-state quantifier and mask retained there. No desired bound is a
premise. The system equality and existing low filter provide the two final
interfaces. No historical theorem or proof chain is copied into this module.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section

namespace AESConcrete.AllStepCaps
open AESMixing
open AESConcrete.RefinedStepZeros (physicalBlock)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L H)

set_option maxRecDepth 100000

/-- The exact complement of the unchanged 177-cell core. -/
def supplementPair (i j : Fin 14) : Prop :=
  (i = 8 ∧ j = 6) ∨ (i = 8 ∧ j = 9) ∨ (i = 8 ∧ j = 7) ∨
  (i = 9 ∧ j = 5) ∨ (i = 9 ∧ j = 8) ∨
  (i = 11 ∧ j = 5) ∨ (i = 11 ∧ j = 6) ∨ (i = 11 ∧ j = 9) ∨
  (i = 12 ∧ j = 12) ∨ (i = 11 ∧ j = 10) ∨ (i = 11 ∧ j = 7) ∨
  (i = 9 ∧ j = 7) ∨ (i = 9 ∧ j = 6) ∨ (i = 9 ∧ j = 10) ∨
  (i = 10 ∧ j = 6) ∨
  (i = 10 ∧ j = 7) ∨ (i = 10 ∧ j = 9) ∨
  (i = 10 ∧ j = 10) ∨ (i = 10 ∧ j = 12)

instance instDecidableSupplementPair (i j : Fin 14) :
    Decidable (supplementPair i j) := by
  unfold supplementPair
  infer_instance

/-- Finite routing coverage; it contains no analytic estimate. -/
theorem core_or_supplement (i j : Fin 14) :
    ResidualLinePlaneStepCaps.certifiedPair i j ∨ supplementPair i j := by
  revert i j
  decide

theorem supplementPair_disjoint (i j : Fin 14) :
    ¬ (ResidualLinePlaneStepCaps.certifiedPair i j ∧ supplementPair i j) := by
  revert i j
  decide

theorem supplementPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => supplementPair ij.1 ij.2)).card = 19 := by decide

/--
Dispatch to the exact individual cap owning each supplemental cell.
-/
theorem supplement_physical_step_cap (i j : Fin 14) (h : supplementPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact WeightedResidualLineStepCaps.physical_8_6_step_cap
  · exact WeightedResidualLineStepCaps.physical_8_9_step_cap
  · exact TwoOutputThreeUniformStepCaps.physical_8_7_step_cap
  · exact WeightedOutputLineStepCaps.physical_9_5_step_cap
  · exact WeightedOutputLineStepCaps.physical_9_8_step_cap
  · exact WeightedThreeOutputStepCaps.physical_11_5_step_cap
  · exact WeightedThreeOutputStepCaps.physical_11_6_step_cap
  · exact WeightedThreeOutputStepCaps.physical_11_9_step_cap
  · exact CoupledTripleStepCaps.physical_12_12_step_cap
  · exact TwoUniformThreeOutputStepCaps.physical_11_10_step_cap
  · exact ThreeUniformThreeOutputStepCaps.physical_11_7_step_cap
  · exact OmittedUniformTwoOutputStepCaps.physical_9_7_step_cap
  · exact OmittedUniformTwoInputStepCaps.physical_9_6_step_cap
  · exact OmittedUniformTwoInputPairStepCaps.physical_9_10_step_cap
  · exact TwoOmittedOutputStepCaps.physical_10_6_step_cap
  · exact TwoOmittedThreeInputStepCaps.physical_10_7_step_cap
  · exact OmittedPairOneInputStepCaps.physical_10_9_step_cap
  · exact TwoOmittedTwoInputStepCaps.physical_10_10_step_cap
  · exact TwoOmittedOneInputStepCaps.physical_10_12_step_cap

/-- Unconditional actual physical step bound for every ordered index pair. -/
theorem physical_step_cap (i j : Fin 14) :
    ‖kernelOperator (physicalBlock i j)‖ ≤ lambda * L i j := by
  rcases core_or_supplement i j with hcore | hsupplement
  · exact ResidualLinePlaneStepCaps.physical_step_cap i j hcore
  · exact supplement_physical_step_cap i j hsupplement

/-- The physical system uses the identical actual step operator. -/
theorem system_step_cap (i j : Fin 14) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤ lambda * L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j

/-- The existing low flag filters L to H; high-source low maps are zero. -/
theorem system_low_cap (i j : Fin 14) :
    ‖PhysicalProjectionSystem.system.low i j‖ ≤ lambda * H i j :=
  PhysicalLowHigh.low_caps_of_step_caps physical_step_cap i j

end AESConcrete.AllStepCaps
