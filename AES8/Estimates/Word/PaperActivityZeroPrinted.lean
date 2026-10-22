import AES8.Estimates.Transfer.PaperActivityPrintedScalars

/-! The raw degree-zero energy bound from the paper's activity spectrum.
The input projection is retained in the energy on the right. Both fixed
components vanish only under explicit zero-value and total-mass hypotheses.
No rational Gram certificate is used. Constructive mathematics only. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityZeroPrinted
open AESMixing PaperKernelBounds PaperActivityFullCompression
open PaperActivityPhysicalJoin PaperActivityPrintedScalars
open AESConcrete.DegreeCentering (distinguishedState globalUniformKernel
  globalUniformKernel_action_eq_zero)
set_option autoImplicit false
set_option maxRecDepth 8192

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Removing both fixed components leaves the literal raw diffusion sandwich. -/
theorem fullCentered_action (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (fullCenteredKernel L.toAddMonoidHom) f =
      degreeTransfer 0 0 0 L.toEquiv f := by
  have hU := globalUniformKernel_action_eq_zero (0 : V) f hz hs
  rw [fullCenteredKernel, kernel_action_sub, kernel_action_add,
    zero_state_action f hz, hU]
  simp only [zero_add, sub_zero, kernelCompose_action, degreeKernel_action]
  funext y
  conv_rhs => rw [degreeTransfer, ← degreeKernel_action]
  change (∑ z, degreeKernel (0 : V) 0 y (L z) * degreeComponent 0 0 f z) =
    ∑ z, degreeKernel (0 : V) 0 y z * degreeComponent 0 0 f (L.symm z)
  rw [← L.toEquiv.sum_comp (fun z =>
    degreeKernel (0 : V) 0 y z * degreeComponent 0 0 f (L.symm z))]
  simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, L.symm_apply_apply]

private theorem real_energy_of_norm (K : AES.Word → AES.Word → ℝ)
    (f : AES.Word → ℝ) :
    (∑ y, action K f y ^ 2) ≤ ‖kernelOperator K‖^2 * ∑ x, f x^2 := by
  have h := (kernelOperator K).le_opNorm (WithLp.toLp 2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg (kernelOperator K)) (norm_nonneg (WithLp.toLp 2 f)))).mpr h
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply,
    kernelAction, action] using hs

/-- This is the printed 6.3/256² constant on the projected input. -/
theorem energy (inverse : Bool) (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, degreeTransfer 0 0 0 (byteDiffusionOrientation inverse) f y^2) ≤
      (63/655360 : ℝ)^2 * ∑ x, degreeComponent 0 0 f x^2 := by
  let L := byteDiffusionOrientedAddEquiv inverse
  have hb : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have hc := degreeComponent_centered (0 : BinaryWord 8) hb 0 f hz hs
  have hn : ‖kernelOperator (fullCenteredKernel L.toAddMonoidHom)‖ <
      (63/655360 : ℝ) := by
    rw [full_activity_norm hb _ (byteDiffusionOrientedAddEquiv_zeroMDS inverse)]
    convert byte_radius_bound using 1 <;> norm_num [BinaryWord.card]
  have he := real_energy_of_norm (fullCenteredKernel L.toAddMonoidHom)
    (degreeComponent 0 0 f)
  rw [fullCentered_action L _ hc.1 hc.2] at he
  have hi : degreeComponent (0 : BinaryWord 8) 0 (degreeComponent 0 0 f) =
      degreeComponent 0 0 f := by
    simp only [← degreeKernel_action, ← kernelCompose_action, degreeKernel_compose _ hb]
  have hd : L.toEquiv = byteDiffusionOrientation inverse := by cases inverse <;> rfl
  simp only [degreeTransfer, hi, hd] at he ⊢
  exact he.trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hn.le)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

#print axioms fullCentered_action
#print axioms energy
end AES8.PaperActivityZeroPrinted
