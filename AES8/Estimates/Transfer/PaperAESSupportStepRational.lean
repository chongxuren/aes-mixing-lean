import AES8.Reductions.Support.PaperAESSupportStepBound
import AES8.Estimates.Transfer.PaperRationalSupportLift
import AES8.Reductions.Support.PaperSupportProfileJoin

/-! Concrete graph lifting in the paper's rational units, followed by exact
transport to the fourteen physical profile coordinates. No activity-only
centering or final comparison-map estimate is asserted here. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSupportStepRational
open AESMixing PaperSupportProjection PaperSupportProfileJoin
open PaperAESActivityIdentification
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem stepGraph_nonneg (i a j b : ℕ) : 0 ≤ PaperComparison.stepGraph i a j b := by
  unfold PaperComparison.stepGraph
  dsimp only
  split_ifs
  · unfold PaperComparison.C PaperComparison.E PaperComparison.qp PaperComparison.sqrtQ
    positivity
  · rfl

theorem grouped_norm_le (i t j u : Fin 5) (hju : j.val ≤ u.val)
    (hn : 0 < i.val+j.val) (adjoint : Bool) (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action (actualStep adjoint) (component 0 f j.val u.val)) i.val t.val) ≤
      ((PaperComparison.support i.val t.val j.val u.val PaperComparison.stepGraph : ℝ) /
        4294967296) * l2 (component (0 : AES.Word) f j.val u.val) := by
  exact (PaperAESSupportStepBound.grouped_norm_le i t j u hn adjoint f).trans
    (mul_le_mul_of_nonneg_right
      (PaperRationalSupportLift.coefficient_le i t j u hju PaperComparison.stepGraph
        (fun a b => stepGraph_nonneg i.val a j.val b) 4294967296 (by norm_num))
      (l2_nonneg _))

/-- Literal physical profile estimate before global-uniform centering. -/
theorem profile_norm_le (a b : Fin 14)
    (hn : 0 < SupportProfile.residualDegree a + SupportProfile.residualDegree b)
    (adjoint : Bool) (f : AES.WordState → ℝ) :
    SupportProfile.profile (action (actualStep adjoint) (SupportProfile.component f b)) a ≤
      ((PaperComparison.support (SupportProfile.residualDegree a) (SupportProfile.supportSize a)
        (SupportProfile.residualDegree b) (SupportProfile.supportSize b)
        PaperComparison.stepGraph : ℝ) / 4294967296) * SupportProfile.profile f b := by
  unfold SupportProfile.profile
  simp only [component_eq]
  exact grouped_norm_le (degreeIndex a) (supportIndex a) (degreeIndex b) (supportIndex b)
    (degree_le_support b) hn adjoint f

end AES8.PaperAESSupportStepRational
