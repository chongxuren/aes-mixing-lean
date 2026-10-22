/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperFiberKernel
import AES8.Math.FiberNormalization

/-!
# Paper Lemma 9 with the exact alphabet-power coefficient

This module combines the normalized fiber-compression theorem with the
symbolic normalization identity. The coefficient is exactly the manuscript's
`q^(-(a+b)/2) * sqrt(ρ*κ)`. Numerical resources remain separate hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperFiberKernel

open PaperKernelBounds

variable {𝕜 C D X Y : Type*} [RCLike 𝕜]
  [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq D] [DecidableEq X] [DecidableEq Y]

/-- The displayed paper bound on the literal adjoint composition. The bound
itself is valid for all finite partition maps and chosen normalizers. -/
theorem fiber_kernel_norm_pow (p : C → X) (t : D → Y) (q a b : ℕ)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hM : ∀ c d, 0 ≤ M c d) (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if t d = y then M c d else 0) ≤ κ) :
    ‖(fiberLift p (q ^ a)).adjoint.comp
      ((kernelOperator B).comp (fiberLift t (q ^ b)))‖ ≤
        (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) * Real.sqrt (ρ * κ) := by
  rw [← FiberNormalization.div_sqrt_pow_product]
  exact fiber_kernel_norm_of_partial_sums p t (q ^ a) (q ^ b)
    B M ρ κ hM hdom hrow hcol

/-- Full paper specialization: the normalized indicators are isometries,
and their actual compression obeys the exact bound. Real and complex kernels,
zero fiber dimensions and empty index types are all included. -/
theorem paper_fiber_kernel_norm_pow (p : C → X) (t : D → Y) (q a b : ℕ)
    (hq : 0 < q)
    (hp : ∀ x, Fintype.card {c : C // p c = x} = q ^ a)
    (ht : ∀ y, Fintype.card {d : D // t d = y} = q ^ b)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hM : ∀ c d, 0 ≤ M c d) (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if t d = y then M c d else 0) ≤ κ) :
    (∀ f : EuclideanSpace 𝕜 X, ‖fiberLift p (q ^ a) f‖ = ‖f‖) ∧
    (∀ f : EuclideanSpace 𝕜 Y, ‖fiberLift t (q ^ b) f‖ = ‖f‖) ∧
    ‖(fiberLift p (q ^ a)).adjoint.comp
      ((kernelOperator B).comp (fiberLift t (q ^ b)))‖ ≤
        (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) * Real.sqrt (ρ * κ) := by
  exact ⟨fiberLift_norm p (q ^ a) (pow_pos hq _) hp,
    fiberLift_norm t (q ^ b) (pow_pos hq _) ht,
    fiber_kernel_norm_pow p t q a b B M ρ κ hM hdom hrow hcol⟩

end AES8.PaperFiberKernel
