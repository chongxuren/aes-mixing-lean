/- Module role: Selected concrete high-return estimates.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Return.ReturnDegreeFour

/-!
# High-return cells from the admitted all-step caps

The actual intermediate high projection is exactly the sum of components
11, 12 and 13.  The existing centered physical step caps bound both legs of
each of these three terms.  Their sum fits the authoritative `M` coefficient
in the twenty cells listed by `Covered`; no old return-table cap is imported.

The endpoint applies to arbitrary joint real input functions.  It supplies
only the listed high-field cells of `TransferAssembly.PhysicalCaps`, with
the centered update and actual middle high projection retained.  Other
return cells, the first high remainder and the complete AES theorem remain
separate obligations.  Constructive proof work only; no attacks or edits to
the predecessor, existing request sources or manuscript.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.constructorNameAsVariable false

noncomputable section

namespace AES8.ComposedReturn
open AESMixing AESMixing.AES AESConcrete
open AES8.SupportProfile
open AES8.TransferAssembly (centeredStep highReturn physicalCoeff returnCoeff)

/-- The exact finite set selected by the ordinary three-high composition bound. -/
def Covered (i j : Fin 14) : Prop :=
  (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) ∨ (i = 6 ∧ j = 3) ∨
  (i = 7 ∧ j = 3) ∨ (i = 8 ∧ j = 3) ∨ (i = 9 ∧ j = 3) ∨
  (i = 10 ∧ j = 3) ∨ (i = 11 ∧ j = 0) ∨ (i = 11 ∧ j = 3) ∨
  (i = 12 ∧ j = 2) ∨ (i = 12 ∧ j = 3) ∨
  (i = 13 ∧ j = 0) ∨ (i = 13 ∧ j = 1) ∨ (i = 13 ∧ j = 2) ∨
  (i = 13 ∧ j = 3) ∨ (i = 13 ∧ j = 4) ∨ (i = 13 ∧ j = 7) ∨
  (i = 13 ∧ j = 8) ∨ (i = 13 ∧ j = 10) ∨ (i = 13 ∧ j = 13)

instance instDecidableCovered (i j : Fin 14) : Decidable (Covered i j) := by
  unfold Covered
  infer_instance

/-- Coverage is finite routing information, not an analytic premise. -/
theorem covered_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => Covered ij.1 ij.2)).card = 20 := by decide

/-- Sum of the three physical two-step coefficient products. -/
def composedCoeff (i j : Fin 14) : ℝ :=
  AESRound.Terminal.lambda ^ 2 *
    (AESRound.Certificate.L i 11 * AESRound.Certificate.L 11 j +
      AESRound.Certificate.L i 12 * AESRound.Certificate.L 12 j +
      AESRound.Certificate.L i 13 * AESRound.Certificate.L 13 j)

private theorem old_step_cap (i j : Fin 14) :
    ‖LegacyTransfer.euclideanBlock i j‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L i j := by
  rw [LowTransfer.euclideanBlock_eq_legacy]
  exact AllStepCaps.physical_step_cap i j

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

/-- Analytic majorant for every actual centered high-return cell. -/
theorem return_majorant (f : WordState → ℝ) (i j : Fin 14) :
    profile (highReturn (component f j)) i ≤ composedCoeff i j * profile f j := by
  have h11 := two_steps_profile_le f i 11 j (old_step_cap i 11) (old_step_cap 11 j)
  have h12 := two_steps_profile_le f i 12 j (old_step_cap i 12) (old_step_cap 12 j)
  have h13 := two_steps_profile_le f i 13 j (old_step_cap i 13) (old_step_cap 13 j)
  rw [ReturnDegreeFour.highReturn_eq_three]
  calc
    profile
        (centeredStep (component (centeredStep (component f j)) 11) +
          centeredStep (component (centeredStep (component f j)) 12) +
          centeredStep (component (centeredStep (component f j)) 13)) i ≤
        profile
          (centeredStep (component (centeredStep (component f j)) 11) +
            centeredStep (component (centeredStep (component f j)) 12)) i +
          profile (centeredStep (component (centeredStep (component f j)) 13)) i :=
      TransferAssembly.profile_add_le _ _ i
    _ ≤
        (profile (centeredStep (component (centeredStep (component f j)) 11)) i +
          profile (centeredStep (component (centeredStep (component f j)) 12)) i) +
          profile (centeredStep (component (centeredStep (component f j)) 13)) i :=
      add_le_add (TransferAssembly.profile_add_le _ _ i) le_rfl
    _ ≤
        ((AESRound.Terminal.lambda * AESRound.Certificate.L i 11) *
          (AESRound.Terminal.lambda * AESRound.Certificate.L 11 j)) * profile f j +
        ((AESRound.Terminal.lambda * AESRound.Certificate.L i 12) *
          (AESRound.Terminal.lambda * AESRound.Certificate.L 12 j)) * profile f j +
        ((AESRound.Terminal.lambda * AESRound.Certificate.L i 13) *
          (AESRound.Terminal.lambda * AESRound.Certificate.L 13 j)) * profile f j :=
      add_le_add (add_le_add h11 h12) h13
    _ = composedCoeff i j * profile f j := by
      unfold composedCoeff
      ring

-- These finite inequalities use the current M and diagonal d directly.
-- The nine enlarged low-matrix entries do not enter this comparison.
-- The scalar screen selects candidates; norm_num proves each cell here.
/-- Exact comparison between the composed physical cap and the current allowance. -/
theorem composed_coefficient_le (i j : Fin 14) (h : Covered i j) :
    composedCoeff i j ≤ physicalCoeff 2 i j (returnCoeff i j) := by
  rcases h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [TransferAssembly.physicalCoeff, TransferAssembly.returnCoeff, AES8.M,
      ReturnDegreeFour.allSum_basis]
    norm_num [composedCoeff, AESRound.Terminal.lambda, AESRound.Certificate.L,
      TransferAssembly.physicalCoeff, TransferAssembly.returnCoeff,
      TransferAssembly.basis, AES8.M, M0, allSum, omega41, d, vec14_apply,
      Fin.sum_univ_succ, Fin.ext_iff]

/-- The listed high-field cells of `PhysicalCaps`, with no estimate premise. -/
theorem high_profile_cap (f : WordState → ℝ) (i j : Fin 14) (h : Covered i j) :
    profile (highReturn (component f j)) i ≤
      physicalCoeff 2 i j (returnCoeff i j) * profile f j :=
  (return_majorant f i j).trans
    (mul_le_mul_of_nonneg_right (composed_coefficient_le i j h) (profile_nonneg f j))

end AES8.ComposedReturn
