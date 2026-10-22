import AES8.Reductions.Return.PaperAESActivityInputSharpDegree
import AES8.Reductions.Return.PaperAESActivityInputNonzero

/-! Sharp printed activity-input intermediates for the literal complex operator
P_i T(P_0-U) on nonzero states. Exact centering and restriction are imported from
the checked kernel identity, and sharp energy is passed through that identity.
Scalar rounding is isolated from the physical/frame reductions. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputSharpNorm
open AESMixing WordActivityFrame PaperKernelBounds
open PaperActivityInputSharpArithmetic PaperAESActivityInputResponse
open PaperAESActivityIdentification PaperAESActivityInputSharpDegree
open PaperAESActivityInputDegree (inputCoefficients degree_zero_synthesis
  degree_zero_energy_le degree_one_energy)
open PaperAESActivityInputNorm (activityInputKernel activityInput_action decimal decimal_nonneg)
open PaperAESActivityInputNonzero (NonzeroWordState nonzeroBlock nonzeroBlock_eq
  restrict_action restrict_energy_le zeroExtend zeroExtend_energy)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

def energyCap (i : Fin 5) : ℝ := match i.val with
  | 2 => 72*C^6*tau^2/wordQ^3
  | 3 => 64*C^5*tau^2*beta/wordQ^2
  | 4 => C^4*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)
  | _ => 0

theorem energyCap_nonneg (i : Fin 5) : 0 ≤ energyCap i := by
  fin_cases i <;> norm_num [energyCap, C_exact, tau, beta, wordQ]

theorem framed_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) i
      (action (actualStep adjoint) (PaperActivityInputAssembly.synthesize c)) x ^ 2) ≤
      energyCap i * ∑ x, PaperActivityInputAssembly.synthesize c x^2 := by
  fin_cases i
  · exact False.elim (hi rfl)
  · change (∑ x, degreeComponent (0 : AES.Word) 1
      (action (actualStep adjoint) (PaperActivityInputAssembly.synthesize c)) x ^ 2) ≤
        0 * ∑ x, PaperActivityInputAssembly.synthesize c x^2
    rw [degree_one_energy]
    simp only [zero_mul,le_refl]
  · exact degree_two_energy adjoint c
  · exact degree_three_energy adjoint c
  · exact degree_four_energy adjoint c

theorem all_input_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (f : AES.WordState → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) i
      (action (actualStep adjoint) (degreeComponent 0 0 f)) x ^ 2) ≤
      energyCap i * ∑ x, f x^2 := by
  have h := framed_energy i hi adjoint (inputCoefficients f)
  rw [degree_zero_synthesis] at h
  exact h.trans (mul_le_mul_of_nonneg_left (degree_zero_energy_le f) (energyCap_nonneg i))

theorem activityInput_real_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (f : AES.WordState → ℝ) :
    (∑ y, action (activityInputKernel i adjoint) f y^2) ≤ energyCap i * ∑ x, f x^2 := by
  rw [activityInput_action]
  exact all_input_energy i hi adjoint f

theorem activityInput_complex_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (f : AES.WordState → ℂ) :
    (∑ y, ‖kernelAction (fun y x => (activityInputKernel i adjoint y x : ℂ)) f y‖^2) ≤
      energyCap i * ∑ x, ‖f x‖^2 :=
  PaperWholeGraphReturn.complex_energy_of_real _ _ (activityInput_real_energy i hi adjoint) f

theorem activityInput_norm_sq (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    ‖kernelOperator (fun y x => (activityInputKernel i adjoint y x : ℂ))‖^2 ≤ energyCap i :=
  operator_norm_sq_le_of_energy _ _ (energyCap_nonneg i)
    (activityInput_complex_energy i hi adjoint)

theorem decimal_square (i : Fin 5) : wordQ^4*energyCap i ≤ decimal i^2 := by
  fin_cases i <;> norm_num [energyCap,decimal,wordQ,tau,beta,C_exact]

/-- Sharp energy on the exact nonzero-domain centered activity input. -/
theorem nonzeroBlock_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (f : NonzeroWordState → ℂ) :
    (∑ y, ‖kernelAction (fun y x => (nonzeroBlock i adjoint y x : ℂ)) f y‖^2) ≤
      energyCap i * ∑ x, ‖f x‖^2 := by
  rw [nonzeroBlock_eq i hi adjoint]
  simp_rw [← restrict_action]
  have h := (restrict_energy_le (kernelAction
    (fun y x => (activityInputKernel i adjoint y x : ℂ)) (zeroExtend f))).trans
    (activityInput_complex_energy i hi adjoint (zeroExtend f))
  simpa only [zeroExtend_energy] using h

theorem nonzeroBlock_norm_sq (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    ‖kernelOperator (fun y x => (nonzeroBlock i adjoint y x : ℂ))‖^2 ≤ energyCap i :=
  operator_norm_sq_le_of_energy _ _ (energyCap_nonneg i)
    (nonzeroBlock_energy i hi adjoint)

/-- The three printed C^6,C^5,C^4 inequalities, with actual operator names. -/
theorem paper_intermediates (adjoint : Bool) :
    ‖kernelOperator (fun y x => (nonzeroBlock 2 adjoint y x : ℂ))‖^2 ≤
      72*C^6*tau^2/wordQ^3 ∧
    ‖kernelOperator (fun y x => (nonzeroBlock 3 adjoint y x : ℂ))‖^2 ≤
      64*C^5*tau^2*beta/wordQ^2 ∧
    ‖kernelOperator (fun y x => (nonzeroBlock 4 adjoint y x : ℂ))‖^2 ≤
      C^4*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2) := by
  exact ⟨nonzeroBlock_norm_sq 2 (by decide) adjoint,
    nonzeroBlock_norm_sq 3 (by decide) adjoint,
    nonzeroBlock_norm_sq 4 (by decide) adjoint⟩

/-- Re-derive the decimals from the sharp route, rather than importing the old cap. -/
theorem nonzeroBlock_scaled_norm (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    wordQ^2 * ‖kernelOperator (fun y x => (nonzeroBlock i adjoint y x : ℂ))‖ ≤ decimal i := by
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg wordQ) (norm_nonneg _)) (decimal_nonneg i)).mp
  calc
    _ = wordQ^4 * ‖kernelOperator (fun y x => (nonzeroBlock i adjoint y x : ℂ))‖^2 := by ring
    _ ≤ wordQ^4*energyCap i := mul_le_mul_of_nonneg_left
      (nonzeroBlock_norm_sq i hi adjoint) (by norm_num [wordQ])
    _ ≤ _ := decimal_square i

/-- Frozen paper1906c42: ordinary H Pi, exact P_0-U, Euclidean nonzero domain. -/
theorem activity_input_paper :
    (∀ i : Fin 5, i ≠ 0 →
      wordQ^2 * ‖kernelOperator (fun y x => (nonzeroBlock i false y x : ℂ))‖ ≤ decimal i) ∧
    decimal 1 = 0 ∧ decimal 2 = (389/10000 : ℝ) ∧
    decimal 3 = (134/10000 : ℝ) ∧ decimal 4 = (1728/1000000 : ℝ) := by
  exact ⟨fun i hi => nonzeroBlock_scaled_norm i hi false,rfl,rfl,rfl,rfl⟩

end AES8.PaperAESActivityInputSharpNorm
