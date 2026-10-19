import AESPaper.ActivityMatrix

/-!
# Energy reduction for finite orthonormal cell indicators

This generic module converts an orthonormal-cell kernel identity and the exact
four-dimensional matrix estimate into an arbitrary-input energy estimate.
Its hypotheses are explicit; the actual AES indicator identity is supplied
separately. No independence premise is required on the input function.
-/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace AESPaper.ActivityEnergy
open AESMixing

variable {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]

def synthesis (v : I → W → ℝ) (b : I → ℝ) (x : W) : ℝ := ∑ a, b a * v a x

def analysis (v : I → W → ℝ) (f : W → ℝ) (a : I) : ℝ := ∑ x, v a x * f x

theorem synthesis_inner (v : I → W → ℝ)
    (hv : ∀ a b, (∑ x, v a x * v b x) = if a = b then 1 else 0)
    (b c : I → ℝ) :
    (∑ x, synthesis v b x * synthesis v c x) = ∑ a, b a * c a := by
  unfold synthesis
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, b a * c j * ∑ x, v a x * v j x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = b a * c a := by simp_rw [hv]; simp

theorem synthesis_energy (v : I → W → ℝ)
    (hv : ∀ a b, (∑ x, v a x * v b x) = if a = b then 1 else 0)
    (b : I → ℝ) : (∑ x, synthesis v b x^2) = ∑ a, b a^2 := by
  simpa only [pow_two] using synthesis_inner v hv b b

theorem analysis_synthesis_inner (v : I → W → ℝ) (f : W → ℝ) (b : I → ℝ) :
    (∑ x, f x * synthesis v b x) = ∑ a, b a * analysis v f a := by
  unfold synthesis analysis
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem analysis_energy_le (v : I → W → ℝ)
    (hv : ∀ a b, (∑ x, v a x * v b x) = if a = b then 1 else 0)
    (f : W → ℝ) : (∑ a, analysis v f a^2) ≤ ∑ x, f x^2 := by
  have hn : 0 ≤ ∑ x, (f x - synthesis v (analysis v f) x)^2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hexp : (∑ x, (f x - synthesis v (analysis v f) x)^2) =
      (∑ x, f x^2) - 2*(∑ x, f x*synthesis v (analysis v f) x) +
      ∑ x, synthesis v (analysis v f) x^2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hexp, analysis_synthesis_inner, synthesis_energy v hv] at hn
  simp only [← pow_two] at hn
  linarith

def liftedKernel (v : I → W → ℝ) (K : I → I → ℝ) (y x : W) : ℝ :=
  ∑ a, ∑ b, K a b * v a y * v b x

theorem liftedKernel_action (v : I → W → ℝ) (K : I → I → ℝ) (f : W → ℝ) :
    action (liftedKernel v K) f = synthesis v (action K (analysis v f)) := by
  funext y
  unfold action liftedKernel synthesis analysis
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem lifted_energy (v : I → W → ℝ)
    (hv : ∀ a b, (∑ x, v a x * v b x) = if a = b then 1 else 0)
    (K : I → I → ℝ) (c : ℝ)
    (hK : ∀ b : I → ℝ, (∑ a, action K b a^2) ≤ c^2 * ∑ a, b a^2)
    (f : W → ℝ) :
    (∑ y, action (liftedKernel v K) f y^2) ≤ c^2 * ∑ x, f x^2 := by
  rw [liftedKernel_action, synthesis_energy v hv]
  exact (hK _).trans (mul_le_mul_of_nonneg_left (analysis_energy_le v hv f) (sq_nonneg c))

theorem activity_lifted_energy (v : Fin 4 → W → ℝ)
    (hv : ∀ a b, (∑ x, v a x * v b x) = if a = b then 1 else 0)
    (f : W → ℝ) :
    (∑ y, action (liftedKernel v ActivityMatrix.matrix) f y^2) ≤
      ((601/100)/ActivityMatrix.q^2)^2 * ∑ x, f x^2 :=
  lifted_energy v hv ActivityMatrix.matrix _ ActivityMatrix.matrix_energy f

end AESPaper.ActivityEnergy
