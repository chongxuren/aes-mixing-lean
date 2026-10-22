import AES8.Estimates.FirstHigh.PaperAESSeveralFirstReturn
import AES8.Reductions.Source.PaperOneSourceReturn

/-! The physical first-return estimate on one fixed active input word.
The two source degrees are split before the return bound is applied, so no
choice of input support is introduced. Only the all-bit entry cap is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESOneFirstReturn
open AESMixing PaperComparison TransferAssembly SupportEvolution
open PaperSupportProjection PaperFixedSupportBlockLift PaperSupportProfileJoin
open PaperAESTwoRoundSource PaperAESTwoRoundProfile
open AESPaper.GroupedLaw (error groupedLaw)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem fixedComponent_above_support {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (z : V) (f : (Fin n → V) → ℝ) (j : ℕ) (s : Fin n → Bool)
    (hj : supportCount s < j) : fixedComponent z f j s = 0 := by
  funext x
  apply Finset.sum_eq_zero
  intro r _
  have h : residualCount r.val ≤ supportCount s :=
    valid_degree_le_support (r.val,s) r.property.1
  rw [r.property.2] at h
  omega

theorem source_decomposition (a : AES.State) (hw : supportCount (sourceMask a) = 1) :
    groupedLaw 0 a =
      fixedComponent (0 : AES.Word) (groupedLaw 0 a) 0 (sourceMask a) +
      fixedComponent (0 : AES.Word) (groupedLaw 0 a) 1 (sourceMask a) := by
  have h := PaperProductSourceSupport.fixed_decomposition 0 AES.wordSuperboxKernel
    AES.word_superbox_pointed (AESPaper.StartingWord.sourceInput a) (sourceMask a)
    (by intro k; simp [sourceMask])
  rw [← grouped_source] at h
  have hz (j : ℕ) (hj : 1 < j) := fixedComponent_above_support (0 : AES.Word)
    (groupedLaw 0 a) j (sourceMask a) (by omega)
  funext x
  simpa [Fin.sum_univ_succ, hz 2 (by omega), hz 3 (by omega), hz 4 (by omega),
    Pi.add_apply] using congrFun h.symm x

def sourceRoot (j : Fin 2) : ℝ := if j = 0 then 1000001/1000000 else 183/500

theorem source_norm_le (a : AES.State) (hw : supportCount (sourceMask a) = 1)
    (j : Fin 2) :
    l2 (fixedComponent (0 : AES.Word) (groupedLaw 0 a) j.val (sourceMask a)) ≤
      sourceRoot j / 65536 := by
  apply (fixed_norm_le a (⟨j.val, by omega⟩ : Fin 5)).trans
  rw [hw]
  apply Real.sqrt_le_iff.mpr
  constructor <;> fin_cases j <;> norm_num [sourceRoot, energyBound, Nat.choose]

theorem coefficient_nonneg (i t j : ℕ) :
    0 ≤ (PaperOneSourceReturn.coefficient i t j : ℝ) := by
  unfold PaperOneSourceReturn.coefficient
  push_cast
  apply mul_nonneg
  · apply mul_nonneg
    · exact_mod_cast rootUpper_nonneg (positionCount i t)
    · exact pow_nonneg (by exact_mod_cast eta_pos.le) _
  · exact PaperRationalSupportLift.supportSum_nonneg i t j 1 returnGraph
      (fun a b => returnGraph_nonneg i a j b)

theorem fixed_return_profile_le (a : AES.State)
    (hw : supportCount (sourceMask a) = 1)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (i : Fin 14) (j : Fin 2) :
    SupportProfile.profile
      (highReturn (fixedComponent 0 (groupedLaw 0 a) j.val (sourceMask a))) i ≤
      ((PaperOneSourceReturn.coefficient (SupportProfile.residualDegree i)
        (SupportProfile.supportSize i) j.val : ℝ) / (q : ℝ)^3) *
          (sourceRoot j / 65536) := by
  rw [ReturnCentering.highReturn_eq_physical_action]
  unfold SupportProfile.profile
  rw [PaperSupportProfileJoin.component_eq]
  apply (PaperOneSourceReturn.norm_le (degreeIndex i) (supportIndex i) j
    (sourceMask a) hw hentry (groupedLaw 0 a)).trans
  exact mul_le_mul_of_nonneg_left (source_norm_le a hw j)
    (div_nonneg (coefficient_nonneg _ _ _) (by norm_num [q]))

theorem normalization (i : Fin 14) (c0 c1 : ℝ) :
    (NormalizedProfile.factor 1 / (1000 * d i)) *
      ((c0 / (q : ℝ)^3) * (sourceRoot 0 / 65536) +
        (c1 / (q : ℝ)^3) * (sourceRoot 1 / 65536)) =
      64 / (125 * d i) * (c0 * (1000001/1000000) + c1 * (183/500)) := by
  unfold NormalizedProfile.factor omega41 q sourceRoot
  norm_num
  ring

theorem firstHigh_le (a : AES.State) (hw : supportCount (sourceMask a) = 1)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (i : Fin 14) :
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * (firstReturn i : ℝ)) := by
  have hc : 0 < NormalizedProfile.factor 1 / (1000 * d i) :=
    div_pos (NormalizedProfile.factor_pos _) (mul_pos (by norm_num) (NormalizedProfile.diagonal_pos i))
  apply le_of_mul_le_mul_left (a := NormalizedProfile.factor 1 / (1000 * d i)) ?_ hc
  rw [PaperAESSeveralFirstReturn.firstHigh_eq_source_return]
  have he : highReturn (groupedLaw 0 a) =
      highReturn (fixedComponent 0 (groupedLaw 0 a) 0 (sourceMask a)) +
      highReturn (fixedComponent 0 (groupedLaw 0 a) 1 (sourceMask a)) := by
    simp only [ReturnCentering.highReturn_eq_physical_action]
    conv_lhs => rw [source_decomposition a hw]
    funext x
    simp [action, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [he]
  calc
    _ ≤ (NormalizedProfile.factor 1 / (1000 * d i)) *
        (SupportProfile.profile (highReturn (fixedComponent 0 (groupedLaw 0 a) 0 (sourceMask a))) i +
         SupportProfile.profile (highReturn (fixedComponent 0 (groupedLaw 0 a) 1 (sourceMask a))) i) :=
      mul_le_mul_of_nonneg_left (profile_add_le _ _ i) hc.le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (fixed_return_profile_le a hw hentry i 0)
        (fixed_return_profile_le a hw hentry i 1)) hc.le
    _ = _ := normalization i _ _
    _ = (PaperFirstReturnComparison.oneSource i : ℝ) := by
      unfold PaperFirstReturnComparison.oneSource
      rw [typeOf_eq]
      push_cast
      have hd : (scales i : ℝ) = d i := congrFun real_scales_eq i
      rw [hd]
      rfl
    _ ≤ (firstReturn i : ℝ) := by
      exact_mod_cast PaperFirstReturnComparison.one_source_le i
    _ = _ := by
      field_simp [(NormalizedProfile.diagonal_pos i).ne', (NormalizedProfile.factor_pos 1).ne']

end AES8.PaperAESOneFirstReturn
