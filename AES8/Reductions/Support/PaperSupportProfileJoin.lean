import AES8.Model.SupportProfile
import AES8.Reductions.Support.PaperSupportProjectionLaws
import AES8.Recurrence.PaperComparisonMaps

/-! The fourteen physical profile coordinates are exactly the paper's grouped
Boolean support projections. Only four-bit masks are enumerated. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportProfileJoin
open AESMixing AESMixing.AES
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def labelEquiv : SupportProfile.Label ≃ PaperSupportProjection.Label 4 :=
  maskBitsEquiv.prodCongr maskBitsEquiv

theorem residualCount_mask : ∀ m : Fin 16,
    PaperSupportProjection.residualCount (maskBit m) = maskSize m := by decide

theorem supportCount_mask : ∀ m : Fin 16,
    PaperSupportProjection.supportCount (maskBit m) = 4-maskSize m := by decide

theorem component_eq (f : AES.WordState → ℝ) (c : Fin 14) :
    SupportProfile.component f c = PaperSupportProjection.component (0 : AES.Word) f
      (SupportProfile.residualDegree c) (SupportProfile.supportSize c) := by
  funext x
  rw [SupportProfile.component_eq_support_residual]
  unfold PaperSupportProjection.component
  rw [← labelEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  change _ = if PaperSupportProjection.residualCount (maskBit p.1) = _ ∧
      PaperSupportProjection.supportCount (maskBit p.2) = _ then _ else 0
  rw [residualCount_mask, supportCount_mask]
  rfl

theorem typeOf_eq : ∀ c : Fin 14, PaperComparison.typeOf c =
    (SupportProfile.residualDegree c, SupportProfile.supportSize c) := by decide

theorem supportSize_lt : ∀ c : Fin 14, SupportProfile.supportSize c < 5 := by decide

theorem residualDegree_lt : ∀ c : Fin 14, SupportProfile.residualDegree c < 5 := by decide

theorem degree_le_support : ∀ c : Fin 14,
    SupportProfile.residualDegree c ≤ SupportProfile.supportSize c := by decide

def degreeIndex (c : Fin 14) : Fin 5 :=
  ⟨SupportProfile.residualDegree c, residualDegree_lt c⟩

def supportIndex (c : Fin 14) : Fin 5 :=
  ⟨SupportProfile.supportSize c, supportSize_lt c⟩

end AES8.PaperSupportProfileJoin
