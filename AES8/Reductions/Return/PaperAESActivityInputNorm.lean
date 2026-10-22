import AES8.Reductions.Return.PaperAESActivityInputDegree
import AES8.Reductions.Return.PaperWholeGraphReturn

/-! Complex Euclidean operator bounds for positive degree after the literal
AES grouped step and the full-space degree-zero projection. NonzeroSpace
centering is identified separately; no quantitative cap is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputNorm
open AESMixing WordActivityFrame PaperActivityInputArithmetic
open PaperAESActivityIdentification PaperAESActivityInputResponse PaperAESActivityInputDegree
open PaperKernelBounds
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

def energyCap (i : Fin 5) : ℝ := match i.val with
  | 2 => 72*loss^2*tau^2/wordQ^3
  | 3 => 64*loss^2*tau^2*beta/wordQ^2
  | 4 => loss^2*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)
  | _ => 0

def decimal (i : Fin 5) : ℝ := match i.val with
  | 2 => 389/10000
  | 3 => 134/10000
  | 4 => 1728/1000000
  | _ => 0

theorem energyCap_nonneg (i : Fin 5) : 0 ≤ energyCap i := by
  fin_cases i <;> norm_num [energyCap,loss,tau,beta,wordQ]
theorem decimal_nonneg (i : Fin 5) : 0 ≤ decimal i := by
  fin_cases i <;> norm_num [decimal]

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

def activityInputKernel (i : Fin 5) (adjoint : Bool) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (degreeKernel 0 i) (kernelCompose (actualStep adjoint) (degreeKernel 0 0))

theorem activityInput_action (i : Fin 5) (adjoint : Bool) (f : AES.WordState → ℝ) :
    action (activityInputKernel i adjoint) f =
      degreeComponent 0 i (action (actualStep adjoint) (degreeComponent 0 0 f)) := by
  simp only [activityInputKernel,kernelCompose_action,degreeKernel_action]

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
  fin_cases i <;> norm_num [energyCap,decimal,wordQ,tau,beta,loss]

/-- The paper's four decimals for the full-space degree-zero input operator. -/
theorem activityInput_scaled_norm (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    wordQ^2 * ‖kernelOperator (fun y x => (activityInputKernel i adjoint y x : ℂ))‖ ≤ decimal i := by
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg wordQ) (norm_nonneg _)) (decimal_nonneg i)).mp
  calc
    _ = wordQ^4 * ‖kernelOperator (fun y x => (activityInputKernel i adjoint y x : ℂ))‖^2 := by ring
    _ ≤ wordQ^4*energyCap i := mul_le_mul_of_nonneg_left
      (activityInput_norm_sq i hi adjoint) (by norm_num [wordQ])
    _ ≤ _ := decimal_square i

end AES8.PaperAESActivityInputNorm
