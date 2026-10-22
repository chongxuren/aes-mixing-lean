import AES8.Reductions.Support.PaperAESSupportReturnBound
import AES8.Recurrence.PaperProfileAssembly

/-! The current paper's high-return matrix bounds the actual AES operator,
subject only to the stated sharp equal-Fourier entry resource. This is the
current PhysicalCaps.high interface, not the historical comparison matrix. -/
noncomputable section
namespace AES8.PaperAESCurrentReturn
open AESMixing PaperComparison PaperSupportProfileJoin TransferAssembly
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem physicalCoeff_eq (a b : Fin 14) :
    physicalCoeff 2 a b (realReturn a b) =
      ((support (SupportProfile.residualDegree a) (SupportProfile.supportSize a)
        (SupportProfile.residualDegree b) (SupportProfile.supportSize b) returnGraph : ℝ) /
        (q : ℝ)^3) := by
  have ha0 : d a ≠ 0 := (NormalizedProfile.diagonal_pos a).ne'
  have hb0 : d b ≠ 0 := (NormalizedProfile.diagonal_pos b).ne'
  have haScale : (scales a : ℝ) = d a := congrFun real_scales_eq a
  have hbScale : (scales b : ℝ) = d b := congrFun real_scales_eq b
  unfold physicalCoeff realReturn returnMatrix
  rw [typeOf_eq a, typeOf_eq b]
  dsimp only
  push_cast
  rw [haScale, hbScale]
  unfold omega41 q
  field_simp [ha0, hb0]
  <;> ring

/-- All 196 entries in the literal current return matrix, including empty
residual sides, act on arbitrary signed joint inputs. -/
theorem high_cap (f : AES.WordState → ℝ) (a b : Fin 14)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    SupportProfile.profile (highReturn (SupportProfile.component f b)) a ≤
      physicalCoeff 2 a b (realReturn a b) * SupportProfile.profile f b := by
  rw [physicalCoeff_eq]
  exact PaperAESSupportReturnBound.profile_norm_le a b hentry f

end AES8.PaperAESCurrentReturn
