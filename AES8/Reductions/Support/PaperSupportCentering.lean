import AES8.Recurrence.TransferAssembly
import AES8.Reductions.Support.PaperSupportProfileJoin
import AES8.Reductions.Return.PaperAESActivityIdentification

/-! Global centering vanishes on a block with positive residual degree on
either side. The activity/activity block is deliberately excluded. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportCentering
open AESMixing AESMixing.AES AES8.TransferAssembly
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem degree_ne_zero (c : Fin 14) (hc : SupportProfile.residualDegree c ≠ 0) :
    SupportDegree.degree c ≠ 0 := by
  intro he
  apply hc
  exact congrArg Fin.val he

theorem component_mass (f : WordState → ℝ) (c : Fin 14)
    (hc : SupportProfile.residualDegree c ≠ 0) :
    (∑ x, SupportProfile.component f c x) = 0 := by
  have h := AESConcrete.DegreeCentering.degreeComponent_sum_zero
    (0 : AES.Word) SupportProfile.word_card_gt_one (SupportDegree.degree c)
    (degree_ne_zero c hc) (SupportProfile.component f c)
  rw [TransferZeros.degree_component] at h
  exact h

theorem uniform_output_component (f : WordState → ℝ) (c : Fin 14)
    (hc : SupportProfile.residualDegree c ≠ 0) :
    SupportProfile.component
      (action (AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word)) f) c = 0 := by
  apply TransferZeros.component_eq_zero_of_degree_eq_zero
  rw [← degreeKernel_action, ← kernelCompose_action,
    AESConcrete.DegreeCentering.degreeKernel_compose_globalUniformKernel
      0 SupportProfile.word_card_gt_one _ (degree_ne_zero c hc), zero_kernel_action]

theorem component_sub (f g : WordState → ℝ) (c : Fin 14) :
    SupportProfile.component (f-g) c =
      SupportProfile.component f c - SupportProfile.component g c := by
  have h := component_add (f-g) g c
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem centered_block_eq (f : WordState → ℝ) (a b : Fin 14)
    (hn : 0 < SupportProfile.residualDegree a + SupportProfile.residualDegree b) :
    SupportProfile.component (centeredStep (SupportProfile.component f b)) a =
      SupportProfile.component
        (action (PaperAESActivityIdentification.actualStep false) (SupportProfile.component f b)) a := by
  rw [PaperAESActivityIdentification.actualStep_ordinary]
  change _ = SupportProfile.component (TransferZeros.physicalWordStep _) a
  rw [TransferZeros.physicalWordStep_eq_step]
  by_cases hb : SupportProfile.residualDegree b = 0
  · have ha : SupportProfile.residualDegree a ≠ 0 := by omega
    rw [centeredStep_formula, component_sub, uniform_output_component _ a ha, sub_zero]
  · rw [centeredStep_eq_step _ (SupportProfile.component_at_zero f b) (component_mass f b hb)]

end AES8.PaperSupportCentering
