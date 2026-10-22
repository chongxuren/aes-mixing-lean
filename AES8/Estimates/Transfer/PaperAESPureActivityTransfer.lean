import AES8.Recurrence.LegacyTransfer
import AES8.Recurrence.PaperComparisonReal
import AES8.Reductions.Support.PaperSupportProfileJoin
import AESConcrete.ActivityFullStep

/-! The sixteen pure-activity entries of the current centered step matrix.
The retained exact MDS counting proof identifies the literal rank-one kernel.
Only the new rational comparison is finite; no historical coefficient is used. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESPureActivityTransfer
open AESMixing AESMixing.AES AESConcrete PaperComparison TransferAssembly
open AESConcrete.ActivityFullStep AESConcrete.ActivityRankOneStep
open AESConcrete.RefinedStepZeros (blockType)
open PaperSupportProfileJoin
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def bound (a b : Fin 14) : ℝ :=
  (activityBound (SupportProfile.supportSize a) (SupportProfile.supportSize b) : ℝ) / (q : ℝ)

theorem scalar_bounds (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) :
    0 ≤ bound a b ∧
      activitySquaredBound (Fintype.card AES.Word) (blockType a).2 (blockType b).2 ≤
        bound a b ^ 2 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [SupportProfile.residualDegree] at ha <;>
    norm_num [SupportProfile.residualDegree] at hb
  all_goals norm_num [bound,activitySquaredBound,AESConcrete.ActivityFullStep.activityCoefficient,
    AESConcrete.ActivityMDSCounts.supportCount,activityMass,
    AES.word_card,BinaryWord.card,blockType,SupportProfile.supportSize,
    activityBound,activityCount,rootUpper,eta,qp,sqrtQ,q,Nat.choose,Finset.sum_range_succ]

theorem activity_pair (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) : activityPair a b := by
  have he : ∀ c : Fin 14, (blockType c).1.val = SupportProfile.residualDegree c := by decide
  exact ⟨Fin.ext ((he a).trans ha),Fin.ext ((he b).trans hb)⟩

theorem physical_energy (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) (f : WordState → ℝ) :
    (∑ y, action (AESConcrete.RefinedStepZeros.physicalBlock a b) f y ^ 2) ≤
      bound a b ^ 2 * ∑ x, f x^2 := by
  rw [physical_activity_rank_one a b (activity_pair a b ha hb)]
  have he := rank_one_scalar_energy_le (activityIndicator (V := AES.Word) (blockType a).2)
    (activityIndicator (blockType b).2)
    (AESConcrete.ActivityFullStep.activityCoefficient (Fintype.card AES.Word) (blockType a).2 (blockType b).2) f
  rw [activityIndicator_energy (by rw [AES.word_card]; norm_num),
    activityIndicator_energy (by rw [AES.word_card]; norm_num)] at he
  exact he.trans (mul_le_mul_of_nonneg_right (scalar_bounds a b ha hb).2
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem operator_cap (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) :
    ‖LegacyTransfer.euclideanBlock a b‖ ≤ bound a b := by
  change ‖kernelOperator (AESConcrete.RefinedStepZeros.physicalBlock a b)‖ ≤ _
  exact kernelOperator_norm_le _ (scalar_bounds a b ha hb).1 (physical_energy a b ha hb)

theorem physicalCoeff_eq (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) :
    physicalCoeff 1 a b (realStep a b) = bound a b := by
  have ha0 := (NormalizedProfile.diagonal_pos a).ne'
  have hb0 := (NormalizedProfile.diagonal_pos b).ne'
  have has : (scales a : ℝ) = d a := congrFun real_scales_eq a
  have hbs : (scales b : ℝ) = d b := congrFun real_scales_eq b
  unfold physicalCoeff realStep stepMatrix bound
  rw [typeOf_eq a,typeOf_eq b]
  dsimp only
  rw [ha,hb]
  simp only [Nat.zero_le,if_true,stepComponent,and_self]
  push_cast
  rw [has,hbs]
  unfold omega41 q
  field_simp [ha0,hb0]
  <;> ring

theorem low_activity_cap (f : WordState → ℝ) (a b : Fin 14)
    (ha : SupportProfile.residualDegree a = 0)
    (hb : SupportProfile.residualDegree b = 0) :
    SupportProfile.profile (centeredStep (SupportProfile.component f b)) a ≤
      physicalCoeff 1 a b (realStep a b) * SupportProfile.profile f b := by
  rw [physicalCoeff_eq a b ha hb]
  exact LegacyTransfer.profile_le_of_operator_cap f a b (operator_cap a b ha hb)

end AES8.PaperAESPureActivityTransfer
