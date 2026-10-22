import AES8.Reductions.Return.PaperAESActivityInputNorm
import AES8.Estimates.Transfer.PaperAESResidualTransfer

/-! Positive-output columns of the current one-step map for activity inputs.
The graph estimate and activity estimate bound the same projected input; their
minimum is therefore legitimate. Pure activity-to-activity blocks are separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityTransfer
open AESMixing AESMixing.AES PaperComparison TransferAssembly
open PaperAESActivityInputNorm PaperAESActivityInputResponse
open PaperAESActivityIdentification PaperSupportProfileJoin
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem degree_norm_le (i : Fin 5) (hi : i ≠ 0) (f : WordState → ℝ) :
    l2 (degreeComponent (0 : AES.Word) i
      (action (actualStep false) (degreeComponent 0 0 f))) ≤
      (decimal i / wordQ^2) * l2 f := by
  have hc : Real.sqrt (energyCap i) ≤ decimal i / wordQ^2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (decimal_nonneg i) (sq_nonneg _)
    · rw [div_pow]
      apply (le_div_iff₀ (by norm_num [wordQ] : 0 < (wordQ^2)^2)).mpr
      nlinarith [decimal_square i]
  have hn : l2 (degreeComponent (0 : AES.Word) i
      (action (actualStep false) (degreeComponent 0 0 f))) ≤
      Real.sqrt (energyCap i) * l2 f := by
    apply (sq_le_sq₀ (l2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (energyCap_nonneg i),l2_sq,l2_sq]
    exact all_input_energy i hi false f
  exact hn.trans (mul_le_mul_of_nonneg_right hc (l2_nonneg _))

theorem activity_profile_le (f : WordState → ℝ) (a b : Fin 14)
    (ha : SupportProfile.residualDegree a ≠ 0)
    (hb : SupportProfile.residualDegree b = 0) :
    SupportProfile.profile (centeredStep (SupportProfile.component f b)) a ≤
      ((activityInput (SupportProfile.residualDegree a) : ℝ) / (q : ℝ)^2) *
        SupportProfile.profile f b := by
  have hba : SupportDegree.degree b = 0 := Fin.ext hb
  have hfix : degreeComponent (0 : AES.Word) 0 (SupportProfile.component f b) =
      SupportProfile.component f b := by
    rw [← hba,TransferZeros.degree_component]
  have h := degree_norm_le (SupportDegree.degree a)
    (PaperSupportCentering.degree_ne_zero a ha) (SupportProfile.component f b)
  rw [hfix] at h
  have he : decimal (SupportDegree.degree a) =
      (activityInput (SupportProfile.residualDegree a) : ℝ) := by
    fin_cases a <;> norm_num [decimal,activityInput,SupportDegree.degree,
      SupportProfile.residualDegree]
  rw [he] at h
  have hc := SupportDegree.profile_le_degree
    (action (actualStep false) (SupportProfile.component f b)) a
  have hcent := PaperSupportCentering.centered_block_eq f a b (by omega)
  unfold SupportProfile.profile at hcent ⊢
  rw [hcent]
  exact hc.trans (by simpa [wordQ,q,SupportProfile.profile] using h)

theorem physicalCoeff_eq (a b : Fin 14)
    (ha : SupportProfile.residualDegree a ≠ 0)
    (hb : SupportProfile.residualDegree b = 0) :
    physicalCoeff 1 a b (realStep a b) =
      min ((support (SupportProfile.residualDegree a) (SupportProfile.supportSize a)
          0 (SupportProfile.supportSize b) stepGraph : ℝ) / (q : ℝ))
        ((activityInput (SupportProfile.residualDegree a) : ℝ) / (q : ℝ)^2) := by
  have ha0 := (NormalizedProfile.diagonal_pos a).ne'
  have hb0 := (NormalizedProfile.diagonal_pos b).ne'
  have has : (scales a : ℝ) = d a := congrFun real_scales_eq a
  have hbs : (scales b : ℝ) = d b := congrFun real_scales_eq b
  unfold physicalCoeff realStep stepMatrix
  rw [typeOf_eq a,typeOf_eq b]
  dsimp only
  rw [hb]
  simp only [Nat.zero_le,if_true,stepComponent,ha,false_and,if_false]
  push_cast
  rw [has,hbs]
  have hq : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  have hs (s : ℝ) : omega41^1 * d a / d b * (512 * (d b / d a) * s) =
      s / (q : ℝ) := by
    unfold omega41 q
    field_simp [ha0,hb0]
    <;> ring
  rw [hs,← min_div_div_right hq.le]
  congr 1
  ring

/-- The forty positive-output entries in the four activity-input columns. -/
theorem low_activity_positive_cap (f : WordState → ℝ) (a b : Fin 14)
    (ha : SupportProfile.residualDegree a ≠ 0)
    (hb : SupportProfile.residualDegree b = 0) :
    SupportProfile.profile (centeredStep (SupportProfile.component f b)) a ≤
      physicalCoeff 1 a b (realStep a b) * SupportProfile.profile f b := by
  rw [physicalCoeff_eq a b ha hb,min_mul_of_nonneg _ _ (SupportProfile.profile_nonneg f b)]
  apply le_min
  · have hg := PaperAESSupportStepRational.profile_norm_le a b (by omega) false f
    have he := PaperSupportCentering.centered_block_eq f a b (by omega)
    unfold SupportProfile.profile at hg ⊢
    rw [he]
    simpa [hb,q] using hg
  · exact activity_profile_le f a b ha hb

end AES8.PaperAESActivityTransfer
