/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperKernelBounds
import AES8.Math.FiberIncidence
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Structural fiber-sum compression bound

This file proves the revised manuscript Lemma 9 (`lem:kernel-sums`).
The row and column hypotheses concern the raw kernel summed over one entire
fiber and the whole opposite code.  The two fiber partitions are aggregated
before applying `PaperKernelBounds.schur_operator_norm_sq`.

The coefficient is literally `1 / (sqrt m * sqrt n)`.  Both the normalized
indicator maps and the actual continuous-linear-map adjoint are identified
with their finite-sum formulas.  Equal positive fiber cardinalities justify
the word isometry; the compression algebra and bound require no constancy
assumption on an input vector, and also work for empty finite types.

The real-power spelling of this coefficient for `m = q^a`, `n = q^b`
belongs to a separate normalization bridge.  Constructive proofs only;
no attacks, manuscript edits, or vendor changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperFiberKernel

open PaperKernelBounds

variable {𝕜 C D X Y : Type*} [RCLike 𝕜]
  [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
  [DecidableEq C] [DecidableEq D] [DecidableEq X] [DecidableEq Y]

/-- Sum of the raw kernel over the two indicated fibers. -/
def rawCompression (p : C → X) (q : D → Y) (B : C → D → 𝕜)
    (x : X) (y : Y) : 𝕜 :=
  ∑ c, if p c = x then ∑ d, if q d = y then B c d else 0 else 0

/-- Each right codeword occurs in exactly one right fiber. -/
theorem rawCompression_row (p : C → X) (q : D → Y) (B : C → D → 𝕜)
    (x : X) :
    (∑ y, rawCompression p q B x y) =
      ∑ c, if p c = x then ∑ d, B c d else 0 := by
  unfold rawCompression
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p c = x
  · simp only [hc, if_true]
    rw [Finset.sum_comm]
    simp
  · simp [hc]

/-- Each left codeword occurs in exactly one left fiber. -/
theorem rawCompression_col (p : C → X) (q : D → Y) (B : C → D → 𝕜)
    (y : Y) :
    (∑ x, rawCompression p q B x y) =
      ∑ c, ∑ d, if q d = y then B c d else 0 := by
  unfold rawCompression
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

/-- The double fiber sum with the two normalized-indicator factors. -/
def compressedKernel (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (x : X) (y : Y) : 𝕜 :=
  rawCompression p q B x y /
    ((Real.sqrt (m : ℝ) : 𝕜) * (Real.sqrt (n : ℝ) : 𝕜))

/-- Nonnegativity is preserved by compression. -/
theorem compressedKernel_nonneg (p : C → X) (q : D → Y) (m n : ℕ)
    (M : C → D → ℝ) (hM : ∀ c d, 0 ≤ M c d) (x : X) (y : Y) :
    0 ≤ compressedKernel p q m n M x y := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro c _
    split_ifs
    · apply Finset.sum_nonneg
      intro d _
      split_ifs
      · exact hM c d
      · exact le_rfl
    · exact le_rfl
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The normalized row sum is exactly the raw partial sum divided by the
two square-root fiber factors.  No fiber-cardinality premise is hidden. -/
theorem compressedKernel_row (p : C → X) (q : D → Y) (m n : ℕ)
    (M : C → D → ℝ) (x : X) :
    (∑ y, compressedKernel p q m n M x y) =
      (∑ c, if p c = x then ∑ d, M c d else 0) /
        (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  simp only [compressedKernel, ← Finset.sum_div]
  rw [rawCompression_row]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- The analogous exact normalized column sum. -/
theorem compressedKernel_col (p : C → X) (q : D → Y) (m n : ℕ)
    (M : C → D → ℝ) (y : Y) :
    (∑ x, compressedKernel p q m n M x y) =
      (∑ c, ∑ d, if q d = y then M c d else 0) /
        (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  simp only [compressedKernel, ← Finset.sum_div]
  rw [rawCompression_col]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- Taking the norm of each fiber block commutes with its majorization. -/
theorem norm_rawCompression_le (p : C → X) (q : D → Y)
    (B : C → D → 𝕜) (M : C → D → ℝ)
    (hdom : ∀ c d, ‖B c d‖ ≤ M c d) (x : X) (y : Y) :
    ‖rawCompression p q B x y‖ ≤ rawCompression p q M x y := by
  unfold rawCompression
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro c _
  by_cases hc : p c = x
  · simp only [hc, if_true]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro d _
    by_cases hd : q d = y
    · simpa only [hd, if_true] using hdom c d
    · simp [hd]
  · simp [hc]

/-- The compressed real majorant dominates every compressed real/complex
kernel.  The denominator is nonnegative, including at zero cardinalities. -/
theorem norm_compressedKernel_le (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (M : C → D → ℝ)
    (hdom : ∀ c d, ‖B c d‖ ≤ M c d) (x : X) (y : Y) :
    ‖compressedKernel p q m n B x y‖ ≤ compressedKernel p q m n M x y := by
  simp only [compressedKernel, norm_div, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (norm_rawCompression_le p q B M hdom x y)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The literal normalized indicator matrix. -/
def liftKernel (p : C → X) (m : ℕ) (c : C) (x : X) : 𝕜 :=
  if p c = x then (Real.sqrt (m : ℝ) : 𝕜)⁻¹ else 0

/-- The manuscript's `J_C`, acting between counting Euclidean spaces. -/
def fiberLift (p : C → X) (m : ℕ) :
    EuclideanSpace 𝕜 X →L[𝕜] EuclideanSpace 𝕜 C :=
  kernelOperator (liftKernel p m)

/-- The map really pulls a vector back along the partition and normalizes it. -/
@[simp] theorem fiberLift_apply (p : C → X) (m : ℕ)
    (f : EuclideanSpace 𝕜 X) (c : C) :
    fiberLift p m f c = f (p c) / (Real.sqrt (m : ℝ) : 𝕜) := by
  change (∑ x, (if p c = x then (Real.sqrt (m : ℝ) : 𝕜)⁻¹ else 0) * f x) = _
  simp [ite_mul, div_eq_mul_inv, mul_comm]

/-- Matrix conjugate transpose agrees with the actual Hilbert-space adjoint. -/
theorem kernelOperator_adjoint (B : C → D → 𝕜) :
    (kernelOperator B).adjoint = kernelOperator (Matrix.conjTranspose B) := by
  unfold kernelOperator
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- The actual adjoint of `J_C` is the normalized fiber sum, with conjugation
handled by the real-valued indicator coefficients. -/
@[simp] theorem fiberLift_adjoint_apply (p : C → X) (m : ℕ)
    (g : EuclideanSpace 𝕜 C) (x : X) :
    (fiberLift p m).adjoint g x =
      (∑ c, if p c = x then g c else 0) / (Real.sqrt (m : ℝ) : 𝕜) := by
  rw [fiberLift, kernelOperator_adjoint]
  change (∑ c, star (liftKernel p m c x) * g c) = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p c = x
  · simp [liftKernel, hc, RCLike.star_def, div_eq_mul_inv, mul_comm]
  · simp [liftKernel, hc]

/-- Equal positive fibers make the indicator map an isometry, also over `ℂ`.
This is a cardinality fact, not an input distribution hypothesis. -/
theorem fiberLift_energy (p : C → X) (m : ℕ) (hm : 0 < m)
    (hfiber : ∀ x, Fintype.card {c : C // p c = x} = m)
    (f : EuclideanSpace 𝕜 X) :
    (∑ c, ‖fiberLift p m f c‖ ^ 2) = ∑ x, ‖f x‖ ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  simp only [fiberLift_apply, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg m), ← Finset.sum_div]
  rw [FiberCollision.constant_fiber_sum p m hfiber (fun x => ‖f x‖ ^ 2)]
  field_simp [hmR]

theorem fiberLift_norm (p : C → X) (m : ℕ) (hm : 0 < m)
    (hfiber : ∀ x, Fintype.card {c : C // p c = x} = m)
    (f : EuclideanSpace 𝕜 X) : ‖fiberLift p m f‖ = ‖f‖ := by
  have he : ‖fiberLift p m f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [EuclideanSpace.norm_sq_eq] using fiberLift_energy p m hm hfiber f
  nlinarith [norm_nonneg (fiberLift p m f), norm_nonneg f]

/-- Regroup a matrix action by the right fiber partition. -/
theorem rawCompression_action (p : C → X) (q : D → Y)
    (B : C → D → 𝕜) (f : Y → 𝕜) (x : X) :
    (∑ y, rawCompression p q B x y * f y) =
      ∑ c, if p c = x then ∑ d, B c d * f (q d) else 0 := by
  unfold rawCompression
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : p c = x
  · simp only [hc, if_true]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    simp [ite_mul]
  · simp [hc]

/-- Expanded action of the normalized compressed matrix. -/
theorem compressedKernel_action (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (f : Y → 𝕜) (x : X) :
    kernelAction (compressedKernel p q m n B) f x =
      (∑ c, if p c = x then
        ∑ d, B c d * (f (q d) / (Real.sqrt (n : ℝ) : 𝕜)) else 0) /
          (Real.sqrt (m : ℝ) : 𝕜) := by
  have hscale :
      (∑ c, if p c = x then
        ∑ d, B c d * (f (q d) / (Real.sqrt (n : ℝ) : 𝕜)) else 0) =
      (∑ c, if p c = x then ∑ d, B c d * f (q d) else 0) /
        (Real.sqrt (n : ℝ) : 𝕜) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : p c = x
    · simp only [hc, if_true, mul_div_assoc, Finset.sum_div]
    · simp [hc]
  unfold kernelAction
  simp only [compressedKernel, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [rawCompression_action, hscale, div_div]
  congr 1
  ring

/-- Literal composition identity for the manuscript's actual operators.
Neither equal fibers nor a uniform/constant input vector is assumed. -/
theorem compression_eq_adjoint_comp (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) :
    kernelOperator (compressedKernel p q m n B) =
      (fiberLift p m).adjoint.comp ((kernelOperator B).comp (fiberLift q n)) := by
  ext f x
  simp only [ContinuousLinearMap.comp_apply, fiberLift_adjoint_apply,
    kernelOperator_apply, fiberLift_apply]
  exact compressedKernel_action p q m n B (fun y => f y) x

/-- Schur after aggregating the two partitions.  Explicit nonnegative caps
include empty types, where a vacuous row hypothesis cannot determine a sign. -/
theorem compressedKernel_operator_norm (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hM : ∀ c d, 0 ≤ M c d)
    (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if q d = y then M c d else 0) ≤ κ) :
    ‖kernelOperator (compressedKernel p q m n B)‖ ≤
      Real.sqrt (ρ * κ) / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  let t : ℝ := Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)
  have ht : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound := schur_operator_norm_sq (compressedKernel p q m n B)
    (compressedKernel p q m n M) (ρ / t) (κ / t)
    (div_nonneg hρ ht) (div_nonneg hκ ht)
    (compressedKernel_nonneg p q m n M hM)
    (norm_compressedKernel_le p q m n B M hdom)
    (fun x => by
      rw [compressedKernel_row]
      exact div_le_div_of_nonneg_right (hrow x) ht)
    (fun y => by
      rw [compressedKernel_col]
      exact div_le_div_of_nonneg_right (hcol y) ht)
  have hsq : (Real.sqrt (ρ * κ) / t) ^ 2 = (ρ / t) * (κ / t) := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg hρ hκ)]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) ht)).mp
  change ‖kernelOperator (compressedKernel p q m n B)‖ ^ 2 ≤
    (Real.sqrt (ρ * κ) / t) ^ 2
  rw [hsq]
  exact hbound

/-- The revised Lemma 9 bound, stated for the actual `J_C^* B J_D`.
The normalization and partition structure are definitions and proven identities,
not hypotheses asserting a desired operator bound or factorization. -/
theorem fiber_kernel_norm (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hM : ∀ c d, 0 ≤ M c d)
    (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if q d = y then M c d else 0) ≤ κ) :
    ‖(fiberLift p m).adjoint.comp ((kernelOperator B).comp (fiberLift q n))‖ ≤
      Real.sqrt (ρ * κ) / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  rw [← compression_eq_adjoint_comp]
  exact compressedKernel_operator_norm p q m n B M ρ κ hρ hκ hM hdom hrow hcol

/-- With nonempty outside label types the nonnegative raw partial sums force
both caps nonnegative. -/
theorem partial_sum_caps_nonneg [Nonempty X] [Nonempty Y]
    (p : C → X) (q : D → Y) (M : C → D → ℝ) (ρ κ : ℝ)
    (hM : ∀ c d, 0 ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if q d = y then M c d else 0) ≤ κ) :
    0 ≤ ρ ∧ 0 ≤ κ := by
  classical
  have hρ0 : 0 ≤ ∑ c, if p c = Classical.arbitrary X then ∑ d, M c d else 0 := by
    apply Finset.sum_nonneg
    intro c _
    split_ifs
    · exact Finset.sum_nonneg (fun d _ => hM c d)
    · exact le_rfl
  have hκ0 : 0 ≤ ∑ c, ∑ d, if q d = Classical.arbitrary Y then M c d else 0 := by
    apply Finset.sum_nonneg
    intro c _
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact hM c d
    · exact le_rfl
  exact ⟨hρ0.trans (hrow (Classical.arbitrary X)),
    hκ0.trans (hcol (Classical.arbitrary Y))⟩

/-- All-finite endpoint with exactly the nonnegative-kernel partial-sum
hypotheses.  Empty labels make the compressed map zero; otherwise the caps
are nonnegative by `partial_sum_caps_nonneg`. -/
theorem fiber_kernel_norm_of_partial_sums
    (p : C → X) (q : D → Y) (m n : ℕ)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hM : ∀ c d, 0 ≤ M c d) (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if q d = y then M c d else 0) ≤ κ) :
    ‖(fiberLift p m).adjoint.comp ((kernelOperator B).comp (fiberLift q n))‖ ≤
      Real.sqrt (ρ * κ) / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · letI := hX
    have hz : kernelOperator (compressedKernel p q m n B) = 0 := by
      ext f x
      exact isEmptyElim x
    rw [← compression_eq_adjoint_comp, hz, norm_zero]
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · letI := hX
    rcases isEmpty_or_nonempty Y with hY | hY
    · letI := hY
      have hz : kernelOperator (compressedKernel p q m n B) = 0 := by
        ext f x
        simp [kernelOperator_apply, kernelAction]
      rw [← compression_eq_adjoint_comp, hz, norm_zero]
      exact div_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · letI := hY
      obtain ⟨hρ, hκ⟩ := partial_sum_caps_nonneg p q M ρ κ hM hrow hcol
      exact fiber_kernel_norm p q m n B M ρ κ hρ hκ hM hdom hrow hcol

/-- The manuscript endpoint, including the normalized indicators' isometry
certificates for positive equal fiber cardinalities.  It covers empty finite
types and adds no cap-sign or input-law premise to the manuscript hypotheses. -/
theorem paper_fiber_kernel_norm
    (p : C → X) (q : D → Y) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hp : ∀ x, Fintype.card {c : C // p c = x} = m)
    (hq : ∀ y, Fintype.card {d : D // q d = y} = n)
    (B : C → D → 𝕜) (M : C → D → ℝ) (ρ κ : ℝ)
    (hM : ∀ c d, 0 ≤ M c d) (hdom : ∀ c d, ‖B c d‖ ≤ M c d)
    (hrow : ∀ x, (∑ c, if p c = x then ∑ d, M c d else 0) ≤ ρ)
    (hcol : ∀ y, (∑ c, ∑ d, if q d = y then M c d else 0) ≤ κ) :
    (∀ f : EuclideanSpace 𝕜 X, ‖fiberLift p m f‖ = ‖f‖) ∧
    (∀ f : EuclideanSpace 𝕜 Y, ‖fiberLift q n f‖ = ‖f‖) ∧
    ‖(fiberLift p m).adjoint.comp ((kernelOperator B).comp (fiberLift q n))‖ ≤
      Real.sqrt (ρ * κ) / (Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
  exact ⟨fiberLift_norm p m hm hp, fiberLift_norm q n hn hq,
    fiber_kernel_norm_of_partial_sums p q m n B M ρ κ hM hdom hrow hcol⟩

end AES8.PaperFiberKernel
