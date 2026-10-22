import AES8.Math.PaperSlopeMetricComparison
import AES8.Math.PaperFrameExactEnergy
import AESMixing.DegreeProjectionBounds

/-! Exact degree-zero frame coordinates for an arbitrary joint input over
any256-element alphabet. The effective input metric is bounded by the
original input energy, with both endpoint coefficients retained. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeFrameInput
open AESMixing WordActivityFrame
open AESMixing.AES (maskBit)
open PaperSlopeMetricComparison
open PaperSlopeCoincidenceMatrix PaperSlopeMetric PaperSlopeInputMetric
set_option autoImplicit false
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] [Zero V]

omit [DecidableEq V] [Zero V] in
theorem xi_eq (hq : Fintype.card V = 256) : xi V = (1/16 : ℝ) := by
  unfold xi q
  rw [hq]
  norm_num only [Nat.cast_ofNat]
  rw [show (256 : ℝ) = 16^2 by norm_num, Real.sqrt_sq (by norm_num)]

omit [DecidableEq V] [Zero V] in
theorem frameMetric_eq (hq : Fintype.card V = 256) (s t : Fin 4 → Bool) :
    frameMetric V s t = AESConcrete.ActivityFrame.frameMetric s t := by
  simp only [frameMetric, wordMetric, xi_eq hq,
    AESConcrete.ActivityFrame.frameMetric, AESConcrete.ActivityFrame.byteMetric]

theorem full_energy (hq : Fintype.card V = 256) (u : Fin 16 → ℝ) :
    (∑ x : Fin 4 → V, (∑ A : Fin 16, frameColumn 0 (maskBit A) x * u A)^2) =
      AESConcrete.ActivityEffectiveMetric.fullEnergy u := by
  rw [gram_quadratic]
  have hq' : 1 < Fintype.card V := by omega
  simp only [gram, frame_gram (0 : V) hq', frameMetric_eq hq]
  rfl

def coefficients (f : (Fin 4 → V) → ℝ) (A : Fin 16) : ℝ :=
  ∑ t : Fin 4 → Bool, frameInverse V (maskBit A) t *
    ∑ x : Fin 4 → V, frameColumn 0 t x * f x

theorem degree_zero_synthesis (hq : Fintype.card V = 256)
    (f : (Fin 4 → V) → ℝ) (x : Fin 4 → V) :
    degreeComponent 0 0 f x =
      ∑ A : Fin 16, frameColumn 0 (maskBit A) x * coefficients f A := by
  have hq' : 1 < Fintype.card V := by omega
  rw [degree_zero_action (0 : V) hq']
  dsimp only
  rw [← Equiv.sum_comp maskBitsEquiv]
  apply Finset.sum_congr rfl
  intro A _
  simp only [coefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro y _
  change frameColumn 0 (maskBit A) x * frameInverse V (maskBit A) t *
    (frameColumn 0 t y * f y) = _
  ring

theorem coefficient_metric_le_input (hq : Fintype.card V = 256)
    (f : (Fin 4 → V) → ℝ) :
    quad metric (signedCoefficients (coefficients f)) ≤ ∑ x, f x^2 := by
  rw [metric_eq_effectiveEnergy]
  calc
    _ ≤ AESConcrete.ActivityEffectiveMetric.fullEnergy (coefficients f) :=
      AESConcrete.ActivityEffectiveMetric.effectiveEnergy_le_fullEnergy _
    _ = ∑ x : Fin 4 → V, (degreeComponent 0 0 f x)^2 := by
      rw [← full_energy hq]
      simp_rw [degree_zero_synthesis hq]
    _ ≤ _ := degreeComponent_energy_le (0 : V) (by omega) 0 f

end AES8.PaperSlopeFrameInput
