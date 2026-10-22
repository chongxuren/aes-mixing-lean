import AES8.Math.PaperKernelBounds

/-! Reusable finite orthonormal-column compression in counting measure.
This module depends on no MDS map, activity constants, or numerical tables.
The column Gram identity is the explicit interface. All operator and trace
transfer identities below are proved from it, rather than assumed. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperFiniteOrthonormalCompression
open PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
variable {U : I → X → ℝ}

/-- Finite-column synthesis into the full state space. -/
def synthesize (U : I → X → ℝ) (v : I → ℝ) (x : X) : ℝ :=
  ∑ a : I, U a x * v a

def analyze (U : I → X → ℝ) (f : (X) → ℝ) (a : I) : ℝ :=
  ∑ x, U a x * f x

theorem analyze_synthesize (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (v : I → ℝ) :
    analyze U (synthesize (U := U) v) = v := by
  funext a
  simp only [analyze, synthesize, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : I, (∑ x : X, U a x * U b x) * v b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = v a := by simp [hU]

/-- Orthonormal columns preserve Euclidean energy exactly. -/
theorem synthesis_energy (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (v : I → ℝ) :
    (∑ x : X, synthesize U v x ^ 2) = ∑ a : I, v a ^ 2 := by
  calc
    _ = ∑ a : I, v a * analyze U (synthesize (U := U) v) a := by
      simp only [synthesize, analyze, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [analyze_synthesize hU]; simp only [pow_two]

/-- Finite-rank kernel for an arbitrary compressed matrix. -/
def liftMatrix (U : I → X → ℝ) (A : Matrix (I) (I) ℝ) (y x : X) : ℝ :=
  ∑ a : I, ∑ b : I, U a y * A a b * U b x

theorem lift_action (A : Matrix (I) (I) ℝ) (f : (X) → ℝ) :
    kernelAction (liftMatrix U A) f = synthesize U (A.mulVec (analyze U f)) := by
  funext y
  simp only [kernelAction, liftMatrix, synthesize, Matrix.mulVec, dotProduct,
    analyze, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Orthogonal-coordinate analysis is contractive, for arbitrary joint input. -/
theorem analysis_energy_le (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (f : (X) → ℝ) :
    (∑ a : I, analyze U f a ^ 2) ≤ ∑ x, f x ^ 2 := by
  have hc : (∑ x : X, f x * synthesize U (analyze U f) x) =
      ∑ a : I, analyze U f a ^ 2 := by
    simp only [synthesize, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (∑ x : X, U a x*f x) * analyze U f a := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by simp only [analyze, pow_two]

  have he : (∑ x : X, (f x-synthesize U (analyze U f) x)^2) =
      (∑ x, f x^2) - 2*(∑ a : I, analyze U f a^2) +
        ∑ a : I, analyze U f a^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [synthesis_energy hU]
    have ht : (∑ x : X, 2*f x*synthesize U (analyze U f) x) =
        2*∑ x : X, f x*synthesize U (analyze U f) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [ht, hc]
  have hp := Finset.sum_nonneg (fun x (_ : x ∈ (Finset.univ : Finset (X))) =>
    sq_nonneg (f x-synthesize U (analyze U f) x))
  rw [he] at hp
  linarith

theorem synthesis_norm (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (v : I → ℝ) :
    ‖WithLp.toLp 2 (synthesize (U := U) v)‖ = ‖WithLp.toLp 2 v‖ := by
  have he := synthesis_energy hU v
  have h1 := energy_eq_norm_sq (synthesize (U := U) v)
  have h2 := energy_eq_norm_sq v
  simp only [Real.norm_eq_abs, sq_abs] at h1 h2
  rw [h1, h2] at he
  nlinarith [norm_nonneg (WithLp.toLp 2 (synthesize (U := U) v)),
    norm_nonneg (WithLp.toLp 2 v)]

theorem analysis_norm_le (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (f : (X) → ℝ) :
    ‖WithLp.toLp 2 (analyze U f)‖ ≤ ‖WithLp.toLp 2 f‖ := by
  have he := analysis_energy_le hU f
  have h1 := energy_eq_norm_sq (analyze U f)
  have h2 := energy_eq_norm_sq f
  simp only [Real.norm_eq_abs, sq_abs] at h1 h2
  rw [h1, h2] at he
  nlinarith [norm_nonneg (WithLp.toLp 2 (analyze U f)), norm_nonneg (WithLp.toLp 2 f)]

/-- Exact operator norm transfer: no compression or norm identity is assumed. -/
theorem lift_norm (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (A : Matrix (I) (I) ℝ) :
    ‖kernelOperator (liftMatrix (U := U) A)‖ = ‖kernelOperator A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖WithLp.toLp 2 (kernelAction (liftMatrix U A) (fun x => f x))‖ ≤ _
    rw [lift_action, synthesis_norm hU]
    have hb := (kernelOperator A).le_opNorm (WithLp.toLp 2 (analyze U (fun x => f x)))
    exact hb.trans (mul_le_mul_of_nonneg_left (analysis_norm_le hU (fun x => f x))
      (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have hb := (kernelOperator (liftMatrix (U := U) A)).le_opNorm
      (WithLp.toLp 2 (synthesize (U := U) (fun a => v a)))
    change ‖WithLp.toLp 2 (kernelAction (liftMatrix U A)
      (synthesize (U := U) (fun a => v a)))‖ ≤ _ at hb
    rw [lift_action, analyze_synthesize hU, synthesis_norm hU, synthesis_norm hU] at hb
    exact hb

/-- Hilbert--Schmidt energy also transfers exactly, including signed matrices. -/
theorem lift_square_sum (hU : ∀ a b : I, (∑ x : X, U a x * U b x) = if a = b then 1 else 0) (A : Matrix (I) (I) ℝ) :
    (∑ y : X, ∑ x : X, liftMatrix U A y x ^ 2) =
      ∑ a : I, ∑ b : I, A a b ^ 2 := by
  have hl (x : X) : (fun y : X => liftMatrix U A y x) =
      synthesize U (fun a => ∑ b : I, A a b * U b x) := by
    funext y
    simp only [liftMatrix, synthesize, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Finset.sum_comm]
  simp_rw [show ∀ x : X, (∑ y : X, liftMatrix U A y x ^ 2) =
      ∑ a : I, (∑ b : I, A a b * U b x)^2 by
    intro x
    have he := synthesis_energy hU (fun a => ∑ b : I, A a b * U b x)
    rw [← hl x] at he
    exact he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [synthesize, mul_comm] using
    synthesis_energy hU (fun b => A a b)


end AES8.PaperFiniteOrthonormalCompression
