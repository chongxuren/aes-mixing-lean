import AESPaper.RectangularFourier
import AESMixing.DegreeAdjoint

/-!
# Rectangular transpose, composition, and scale bounds

The accepted EnergyBound predicate quantifies over every real signed input.
The transpose is justified by the exact finite bilinear identity and the
frozen adjoint-energy theorem. Coefficients are squared, so no positivity
premise is needed for these algebraic bounds; numerical norm interpretations
must still use nonnegative coefficients.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RectangularBounds
open AESMixing AESPaper.RectangularFourier

section Finite
variable {Y Z X : Type*} [Fintype Y] [Fintype Z] [Fintype X]

def transpose (M : Y → X → ℝ) : X → Y → ℝ := fun x y => M y x

/-- Transposition concerns the matrix, separately from the adjoint flags of
the residual legs that may occur in its entries. -/
theorem transpose_inner (M : Y → X → ℝ) (f : X → ℝ) (g : Y → ℝ) :
    (∑ y, rectAction M f y * g y) = ∑ x, f x * rectAction (transpose M) g x := by
  unfold rectAction transpose
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem energyBound_transpose (M : Y → X → ℝ) (c : ℝ) (hM : EnergyBound M c) :
    EnergyBound (transpose M) c := by
  intro g
  exact adjoint_energy_le (rectAction M) (rectAction (transpose M)) c
    (transpose_inner M) hM g

theorem energyBound_transpose_iff (M : Y → X → ℝ) (c : ℝ) :
    EnergyBound (transpose M) c ↔ EnergyBound M c := by
  constructor
  · intro h
    exact energyBound_transpose (transpose M) c h
  · exact energyBound_transpose M c

/-- Composition retains the middle source and applies the two arbitrary-input
bounds in their actual order. -/
theorem energyBound_compose (M : Y → Z → ℝ) (N : Z → X → ℝ)
    (a b : ℝ) (hM : EnergyBound M a) (hN : EnergyBound N b) :
    EnergyBound (kernelCompose M N) (a * b) := by
  intro f
  change (∑ y, action (kernelCompose M N) f y ^ 2) ≤ _
  rw [kernelCompose_action]
  have hm := hM (rectAction N f)
  have hn := mul_le_mul_of_nonneg_left (hN f) (sq_nonneg a)
  calc
    _ ≤ a ^ 2 * ∑ z, rectAction N f z ^ 2 := hm
    _ ≤ a ^ 2 * (b ^ 2 * ∑ x, f x ^ 2) := hn
    _ = (a * b) ^ 2 * ∑ x, f x ^ 2 := by ring

omit [Fintype Y] in
theorem rectAction_scale (a : ℝ) (M : Y → X → ℝ) (f : X → ℝ) :
    rectAction (fun y x => a * M y x) f = fun y => a * rectAction M f y := by
  funext y
  simp only [rectAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem energyBound_scale (a : ℝ) (M : Y → X → ℝ) (c : ℝ)
    (hM : EnergyBound M c) :
    EnergyBound (fun y x => a * M y x) (a * c) := by
  intro f
  rw [rectAction_scale]
  have hs : (∑ y : Y, (a * rectAction M f y) ^ 2) =
      a ^ 2 * ∑ y : Y, rectAction M f y ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ a ^ 2 * (c ^ 2 * ∑ x, f x ^ 2) :=
      mul_le_mul_of_nonneg_left (hM f) (sq_nonneg a)
    _ = (a * c) ^ 2 * ∑ x, f x ^ 2 := by ring

end Finite
end AESPaper.RectangularBounds
