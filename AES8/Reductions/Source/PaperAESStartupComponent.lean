import AES8.Reductions.Source.PaperAESStartupResidual
import AES8.Reductions.Source.OneSourceSupport
import AES8.Estimates.Source.PaperStartupScalars

/-!
# Current positive-residual startup component formula

This leaf removes the stationary reference only in positive residual degree,
then transports the actual component energy to the paper's rational formula.
Source reduction and scalar allowance comparison have distinct interfaces.
Constructive only; no attacks or assumed startup/profile bound.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupComponent
open AESMixing AESMixing.AES
open PaperAESStartupSource PaperAESStartupResidual
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Global centering does not alter positive residual-degree components. -/
theorem positive_error_component (a : AES.State) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c) :
    SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c =
      SupportProfile.component (AESPaper.GroupedLaw.groupedLaw 1 a) c := by
  change SupportProfile.component
    (AESPaper.GroupedLaw.groupedLaw 1 a - uniformExcept (0 : WordState)) c = _
  rw [OneSourceSupport.component_sub, OneSourceSupport.uniform_component_eq_zero c hi, sub_zero]

/-- The exact symbolic position formula is the real cast of residualSquared. -/
theorem scaled_pattern_formula (w : ℕ) (i t : Fin 5) (hit : i.val ≤ t.val) :
    (4294967296 : ℝ)^5 *
      (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        patternBound w (4-t.val) i.val) =
      (PaperStartupScalars.residualSquared i.val t.val w : ℚ) := by
  have he : 4-(4-t.val+i.val) = t.val-i.val := by omega
  norm_num [PaperStartupScalars.residualSquared, PaperComparison.positionCount,
    PaperComparison.q, PaperStartupScalars.point, PaperStartupScalars.collision,
    PaperStartupScalars.normSquared, PaperStartupScalars.columnEnergy, patternBound, he]
  ring

/-- The paper's eq. initial-residual, using the actual four-round centered
error, restricted-source response, support indicators and orthogonal sum. -/
theorem actual_residual_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (c : Fin 14) (hi : 0 < SupportProfile.residualDegree c)
    (hw : 4-SupportProfile.supportSize c ≤ (active a).card) :
    (4294967296 : ℝ)^5 *
      (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y ^ 2) ≤
      (PaperStartupScalars.residualSquared (SupportProfile.residualDegree c)
        (SupportProfile.supportSize c) (active a).card : ℚ) := by
  rw [positive_error_component a c hi, PaperSupportProfileJoin.component_eq]
  have h := component_four_round_energy_le raw a (PaperSupportProfileJoin.degreeIndex c)
    (PaperSupportProfileJoin.supportIndex c) (PaperSupportProfileJoin.degree_le_support c) hw
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
    (scaled_pattern_formula (active a).card (PaperSupportProfileJoin.degreeIndex c)
      (PaperSupportProfileJoin.supportIndex c) (PaperSupportProfileJoin.degree_le_support c))

/-- The zero branch is proved on every physical pattern before summation. -/
theorem component_four_round_energy_zero (a : AES.State) (ha : a ≠ 0)
    (i t : Fin 5) (hw : (active a).card ≤ 4-t.val) :
    (∑ y : AES.WordState,
      PaperSupportProjection.component (0 : AES.Word)
        (AESPaper.GroupedLaw.groupedLaw 1 a) i.val t.val y ^ 2) = 0 := by
  rw [PaperSupportBlockLift.component_labels]
  rw [orthogonal_family_energy _ (fun p q hpq =>
    PaperSupportProjection.raw_orthogonal (0 : AES.Word) AESConcrete.AES.word_card_gt_one
      p.val q.val (fun he => hpq (Subtype.ext he)) _ _)]
  apply Finset.sum_eq_zero
  intro p _
  let r := maskBitsEquiv.symm p.val.2
  let out := maskBitsEquiv.symm p.val.1
  have hr : maskBit r = p.val.2 := maskBitsEquiv.apply_symm_apply _
  have ho : maskBit out = p.val.1 := maskBitsEquiv.apply_symm_apply _
  have hd : MaskDisjoint r out := by
    intro k hk ho'
    have hv := p.property.1 k (by simpa only [ho] using ho')
    have hv' : p.val.2 k = true := by simpa only [hr] using hk
    rw [hv] at hv'
    cases hv'
  have hrc : maskSize r = 4-t.val := by
    have h := PaperSupportProfileJoin.supportCount_mask r
    rw [hr, p.property.2.2] at h
    have hl := AESConcrete.RestrictedCoordinateChoices.maskSize_le_four r
    omega
  simpa only [PaperSupportProjection.raw, hr, ho] using
    raw_four_round_energy_zero a ha r out hd (by simpa only [hrc] using hw)

theorem actual_residual_energy_zero (a : AES.State) (ha : a ≠ 0) (c : Fin 14)
    (hi : 0 < SupportProfile.residualDegree c)
    (hw : (active a).card ≤ 4-SupportProfile.supportSize c) :
    (∑ y, SupportProfile.component (AESPaper.GroupedLaw.error 1 a) c y ^ 2) = 0 := by
  rw [positive_error_component a c hi, PaperSupportProfileJoin.component_eq]
  exact component_four_round_energy_zero a ha (PaperSupportProfileJoin.degreeIndex c)
    (PaperSupportProfileJoin.supportIndex c) hw

end AES8.PaperAESStartupComponent
