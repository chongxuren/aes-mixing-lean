import AES8.Math.PaperFiberKernel

/-! Explicit finite coordinate equivalences preserve counting Hilbert norms
and normalized fiber kernels. No dimension/cardinality scaling is introduced. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperKernelReindex
open PaperKernelBounds PaperFiberKernel
set_option autoImplicit false

variable {𝕜 X Y X' Y' C D C' D' : Type*} [RCLike 𝕜]
  [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
  [Fintype C] [Fintype D] [Fintype C'] [Fintype D']
  [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']
  [DecidableEq C] [DecidableEq D] [DecidableEq C'] [DecidableEq D']

theorem reindex_norm (e : X ≃ X') (f : X' → 𝕜) :
    ‖WithLp.toLp 2 (fun x => f (e x))‖ = ‖WithLp.toLp 2 f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  exact e.sum_comp (fun x => ‖f x‖ ^ 2)

theorem kernelAction_reindex (ex : X ≃ X') (ey : Y ≃ Y')
    (K : Y' → X' → 𝕜) (f : X → 𝕜) (y : Y) :
    kernelAction (fun y x => K (ey y) (ex x)) f y =
      kernelAction K (fun x => f (ex.symm x)) (ey y) := by
  unfold kernelAction
  simpa only [Equiv.symm_apply_apply] using
    ex.sum_comp (fun x => K (ey y) x * f (ex.symm x))

theorem kernelOperator_reindex_le (ex : X ≃ X') (ey : Y ≃ Y')
    (K : Y' → X' → 𝕜) :
    ‖kernelOperator (fun y x => K (ey y) (ex x))‖ ≤ ‖kernelOperator K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  let g : EuclideanSpace 𝕜 X' := WithLp.toLp 2 (fun x => f (ex.symm x))
  have he : kernelOperator (fun y x => K (ey y) (ex x)) f =
      WithLp.toLp 2 (fun y => kernelOperator K g (ey y)) := by
    ext y
    exact kernelAction_reindex ex ey K (fun x => f x) y
  rw [he, reindex_norm]
  have hg : ‖g‖ = ‖f‖ := reindex_norm ex.symm (fun x => f x)
  simpa only [hg] using (kernelOperator K).le_opNorm g

theorem kernelOperator_reindex (ex : X ≃ X') (ey : Y ≃ Y')
    (K : Y' → X' → 𝕜) :
    ‖kernelOperator (fun y x => K (ey y) (ex x))‖ = ‖kernelOperator K‖ := by
  apply le_antisymm (kernelOperator_reindex_le ex ey K)
  simpa only [Equiv.apply_symm_apply] using
    kernelOperator_reindex_le ex.symm ey.symm (fun y x => K (ey y) (ex x))

theorem compressedKernel_reindex (ec : C ≃ C') (ed : D ≃ D')
    (ex : X ≃ X') (ey : Y ≃ Y') (p : C → X) (q : D → Y)
    (p' : C' → X') (q' : D' → Y') (B : C → D → 𝕜) (B' : C' → D' → 𝕜)
    (hp : ∀ c, p' (ec c) = ex (p c)) (hq : ∀ d, q' (ed d) = ey (q d))
    (hB : ∀ c d, B' (ec c) (ed d) = B c d) (m n : ℕ) (x : X) (y : Y) :
    compressedKernel p q m n B x y = compressedKernel p' q' m n B' (ex x) (ey y) := by
  unfold compressedKernel
  congr 1
  unfold rawCompression
  rw [← ec.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  simp only [hp, Equiv.apply_eq_iff_eq]
  split_ifs
  · rw [← ed.sum_comp]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hq, Equiv.apply_eq_iff_eq, hB]
  · rfl

theorem real_toComplex_norm {A : Type*} [Fintype A] (f : A → ℝ) :
    ‖WithLp.toLp 2 (fun x => (f x : ℂ))‖ = ‖WithLp.toLp 2 f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Complex.norm_real, Real.norm_eq_abs]

/-- Real matrices keep the same counting norm when real vectors are embedded
in complex coordinates. This direction needs no spectral theorem. -/
theorem real_kernel_norm_le_complex (K : Y → X → ℝ) :
    ‖kernelOperator K‖ ≤ ‖kernelOperator (fun y x => (K y x : ℂ))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  let g : EuclideanSpace ℂ X := WithLp.toLp 2 (fun x => (f x : ℂ))
  have he : kernelOperator (fun y x => (K y x : ℂ)) g =
      WithLp.toLp 2 (fun y => ((kernelOperator K f y : ℝ) : ℂ)) := by
    ext y
    simp only [kernelOperator_apply, kernelAction, Complex.ofReal_sum, Complex.ofReal_mul]
    rfl
  have h := (kernelOperator (fun y x => (K y x : ℂ))).le_opNorm g
  rw [he, real_toComplex_norm] at h
  have hg : ‖g‖ = ‖f‖ := real_toComplex_norm (fun x => f x)
  simpa only [hg] using h

end AES8.PaperKernelReindex
