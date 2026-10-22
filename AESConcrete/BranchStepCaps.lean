import AESConcrete.PartialStepCaps
import AESConcrete.ActivityBranchZeros

/-!
# Partial physical step caps extended by activity branch zeros

Separate candidate interface outside the frozen degree package. It combines
the existing 46 certified cases with 23 additional activity branch zeros.
The predicate describes sufficient proved cases; its complement says
nothing about validity of a smaller frozen cap. Return caps, initialization,
experiment linkage and the complete AES 10/14/16 theorem remain open.
Constructive mathematics only; no attacks or manuscript/historical edits.
-/

-- Local resource overlay for the finite 196-case zero-entry classifier.
-- All mathematical declarations are unchanged; the module wall timeout remains.
set_option maxHeartbeats 0

noncomputable section
open scoped BigOperators

namespace AESConcrete.BranchStepCaps
open AESMixing
open RefinedStepZeros (physicalBlock crossPair blockType)

def certifiedPair (i j : Fin 14) : Prop :=
  PartialStepCaps.certifiedPair i j ∨ ActivityBranchZeros.branchPair i j

instance (i j : Fin 14) : Decidable (certifiedPair i j) := by
  unfold certifiedPair
  infer_instance

theorem physical_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rcases h with h | h
  · exact PartialStepCaps.physical_step_cap i j h
  · exact ActivityBranchZeros.physical_branch_step_cap i j h

theorem system_step_cap (i j : Fin 14) (h : certifiedPair i j) :
    ‖PhysicalProjectionSystem.system.step i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_step_cap i j h

theorem certifiedPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => certifiedPair ij.1 ij.2)).card = 69 := by decide

/-- Exact table coverage is distinct from the operator arguments establishing
the two zero families. No scalar entry is used to prove a physical zero. -/
theorem zero_entry_iff_cross_or_branch (i j : Fin 14) :
    AESRound.Certificate.L i j = 0 ↔ crossPair i j ∨ ActivityBranchZeros.branchPair i j := by
  constructor
  · intro hzero
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Or.inl (by decide)
      | exact Or.inr (by decide)
      | norm_num [AESRound.Certificate.L] at hzero
  · rintro (hcross | hbranch)
    · fin_cases i <;> fin_cases j
      all_goals first | rfl | (exfalso; revert hcross; decide)
    · exact (ActivityBranchZeros.certificate_branch_entries i j hbranch).1

theorem all_zero_entries_certified (i j : Fin 14) (hzero : AESRound.Certificate.L i j = 0) :
    certifiedPair i j := by
  rcases (zero_entry_iff_cross_or_branch i j).mp hzero with hcross | hbranch
  · exact Or.inl (Or.inl hcross)
  · exact Or.inr hbranch

end AESConcrete.BranchStepCaps
