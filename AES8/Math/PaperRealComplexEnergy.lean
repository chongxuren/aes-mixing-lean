import AES8.Math.PaperKernelBounds
import AESMixing.Finite

/-! Real energy bounds extend to complex inputs by separating real and imaginary
parts. This reusable scalar transport is independent of AES graph estimates. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperRealComplexEnergy
open AESMixing
set_option autoImplicit false

/-- Real and imaginary parts preserve the original signed cancellations. -/
theorem complex_energy_of_real {A B : Type*} [Fintype A] [Fintype B]
    (T : A → B → ℝ) (b : ℝ)
    (hreal : ∀ f : B → ℝ, (∑ y, action T f y ^ 2) ≤ b * ∑ x, f x ^ 2)
    (f : B → ℂ) :
    (∑ y, ‖PaperKernelBounds.kernelAction (fun y x => (T y x : ℂ)) f y‖ ^ 2) ≤
      b * ∑ x, ‖f x‖ ^ 2 := by
  have hre (y : A) :
      (PaperKernelBounds.kernelAction (fun y x => (T y x : ℂ)) f y).re =
        action T (fun x => (f x).re) y := by
    simp [PaperKernelBounds.kernelAction, action]
  have him (y : A) :
      (PaperKernelBounds.kernelAction (fun y x => (T y x : ℂ)) f y).im =
        action T (fun x => (f x).im) y := by
    simp [PaperKernelBounds.kernelAction, action]
  simp_rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two, hre, him]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add]
  exact add_le_add (hreal (fun x => (f x).re)) (hreal (fun x => (f x).im))

end AES8.PaperRealComplexEnergy
