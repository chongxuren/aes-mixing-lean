import AES8.Math.PaperActivityInputGram
import AESMixing.L2Sums
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharp conditioning of the actual tensor activity frame

Candidate source; diagnostic and review status is recorded in adjacent receipts. The finite inverse-Gram argument is adapted from the
historical AESPaper.WordActivityFrame; the actual columns, Gram, inverse and
projection identities are imported from the current WordActivityFrame.
The alphabet and signed joint coefficients are arbitrary. No independence,
probability, numerical search, attack or assumed spectral bound is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators

namespace AES8.PaperActivityArrayFrame
open AESMixing WordActivityFrame

section InverseGram
variable {S X : Type*} [Fintype S] [DecidableEq S] [Fintype X]

theorem synthesis_bilinear (A : X → S → ℝ) (c d : S → ℝ) :
    (∑ x, action A c x * action A d x) =
      ∑ s, c s * action (gram A) d s := by
  rw [kernel_bilinear]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ t, c s * d t * gram A s t) = c s * action (gram A) d s
  rw [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Absolute row control permits both signs in the inverse Gram. -/
theorem symmetric_quadratic_le_row_sum (B : S → S → ℝ) (R : ℝ)
    (hsym : ∀ s t, B s t = B t s)
    (hrow : ∀ s, (∑ t, |B s t|) ≤ R) (c : S → ℝ) :
    (∑ s, c s * action B c s) ≤ R * ∑ s, c s ^ 2 := by
  have h := PaperActivityInputGram.symmetric_quadratic_le
    (fun s t => |B s t|) R (fun s t => by rw [hsym s t])
    (fun s t => abs_nonneg _) hrow (fun s => |c s|)
  simp only [sq_abs] at h
  calc
    _ = ∑ s, ∑ t, c s * c t * B s t := by
      simp only [action, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |c s| * |c t| * |B s t| := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      simpa only [abs_mul] using le_abs_self (c s * c t * B s t)
    _ ≤ _ := h

/-- An exact Gram inverse yields a lower synthesis bound by Cauchy--Schwarz. -/
theorem coefficient_energy_le_of_inverse_gram
    (A : X → S → ℝ) (B : S → S → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hsym : ∀ s t, B s t = B t s)
    (hinv : ∀ s t, (∑ u, gram A s u * B u t) = if s = t then 1 else 0)
    (hrow : ∀ s, (∑ t, |B s t|) ≤ R) (c : S → ℝ) :
    (∑ s, c s ^ 2) ≤ R * ∑ x, action A c x ^ 2 := by
  let d : S → ℝ := action B c
  have hcomp : kernelCompose (gram A) B = identityKernel := by
    funext s t
    exact hinv s t
  have hdual : action (gram A) d = c := by
    change action (gram A) (action B c) = c
    rw [← kernelCompose_action, hcomp, identityKernel_action]
  have hpair : (∑ x, action A c x * action A d x) = ∑ s, c s ^ 2 := by
    rw [synthesis_bilinear, hdual]
    simp only [pow_two]
  have hd : (∑ x, action A d x ^ 2) ≤ R * ∑ s, c s ^ 2 := by
    calc
      _ = ∑ s, d s * c s := by
        simpa only [← pow_two, hdual] using synthesis_bilinear A d d
      _ = ∑ s, c s * action B c s := by
        apply Finset.sum_congr rfl
        intro s _
        exact mul_comm _ _
      _ ≤ _ := symmetric_quadratic_le_row_sum B R hsym hrow c
  have hphys : 0 ≤ ∑ x, action A c x ^ 2 := by positivity
  have hcoeff : 0 ≤ ∑ s, c s ^ 2 := by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (action A c) (action A d)
  rw [hpair] at hcs
  have hmain := hcs.trans (mul_le_mul_of_nonneg_left hd hphys)
  by_cases hz : (∑ s, c s ^ 2) = 0
  · rw [hz]
    exact mul_nonneg hR hphys
  · have hpos : 0 < ∑ s, c s ^ 2 := lt_of_le_of_ne hcoeff (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := ∑ s, c s ^ 2) _ hpos
    nlinarith [hmain]
end InverseGram

section Alphabet
variable {V : Type*} [Fintype V]

theorem xi_nonneg : 0 ≤ xi V := by unfold xi; positivity

theorem xi_lt_one (hq : 1 < Fintype.card V) : xi V < 1 := by
  have hx := xi_sq hq
  have hq' := q_gt_one hq
  have hi : 1 / q V < 1 := by
    apply (div_lt_iff₀ (q_pos hq)).mpr
    simpa using hq'
  nlinarith [xi_nonneg (V := V)]

theorem eta_nonneg (hq : 1 < Fintype.card V) : 0 ≤ eta V :=
  div_nonneg (q_pos hq).le (sub_pos.mpr (q_gt_one hq)).le

theorem inverse_row_factor (hq : 1 < Fintype.card V) :
    eta V * (1 + xi V) = (1 - xi V)⁻¹ := by
  rw [← one_div]
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr (xi_lt_one hq)))).mpr
  nlinarith [eta_mul_one_sub_xi_sq hq]

theorem wordInverse_abs_row (hq : 1 < Fintype.card V) (s : Bool) :
    (∑ t : Bool, |wordInverse V s t|) = (1 - xi V)⁻¹ := by
  have h := inverse_row_factor hq
  cases s <;>
    simp [wordInverse, abs_mul, abs_of_nonneg (eta_nonneg hq),
      abs_of_nonneg (xi_nonneg (V := V))] <;> nlinarith [h]

/-- Square-root form; exponent combination will give exactly `-(a+b)/2`. -/
def conditioningFactor (V : Type*) [Fintype V] (n : ℕ) : ℝ :=
  ((Real.sqrt (1 - xi V))⁻¹) ^ n

theorem conditioningFactor_nonneg (n : ℕ) : 0 ≤ conditioningFactor V n := by
  unfold conditioningFactor
  positivity

theorem conditioningFactor_sq (hq : 1 < Fintype.card V) (n : ℕ) :
    conditioningFactor V n ^ 2 = ((1 - xi V)⁻¹) ^ n := by
  unfold conditioningFactor
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, inv_pow,
    Real.sq_sqrt (sub_pos.mpr (xi_lt_one hq)).le]

theorem conditioningFactor_eq_rpow (hq : 1 < Fintype.card V) (n : ℕ) :
    conditioningFactor V n = (1 - xi V) ^ (-(n : ℝ) / 2) := by
  rw [Real.rpow_div_two_eq_sqrt (-(n : ℝ)) (sub_pos.mpr (xi_lt_one hq)).le,
    Real.rpow_neg (Real.sqrt_nonneg _) (n : ℝ), Real.rpow_natCast]
  exact inv_pow _ _

theorem conditioningFactor_mul (a b : ℕ) :
    conditioningFactor V a * conditioningFactor V b = conditioningFactor V (a+b) := by
  simp only [conditioningFactor, pow_add]
end Alphabet

section Tensor
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def synthesize (z : V) (c : (I → Bool) → ℝ) (x : I → V) : ℝ :=
  ∑ s, frameColumn z s x * c s

theorem frameInverse_symmetric (s t : I → Bool) :
    frameInverse V s t = frameInverse V t s := by
  simp only [frameInverse, wordInverse_symmetric]

theorem frameInverse_abs_row (hq : 1 < Fintype.card V) (s : I → Bool) :
    (∑ t : I → Bool, |frameInverse V s t|) =
      ((1 - xi V)⁻¹) ^ Fintype.card I := by
  unfold frameInverse
  simp_rw [Finset.abs_prod]
  rw [← Fintype.prod_sum (fun i t => |wordInverse V (s i) t|)]
  simp_rw [wordInverse_abs_row hq]
  simp only [Finset.prod_const, Finset.card_univ]

/-- Sharp inverse-frame energy for arbitrary signed tensor coefficients. -/
theorem frame_coefficient_energy (z : V) (hq : 1 < Fintype.card V)
    (c : (I → Bool) → ℝ) :
    (∑ s, c s ^ 2) ≤ ((1 - xi V)⁻¹) ^ Fintype.card I *
      ∑ x : I → V, synthesize z c x ^ 2 := by
  apply coefficient_energy_le_of_inverse_gram
    (fun x s => frameColumn z s x) (frameInverse V)
    (((1 - xi V)⁻¹) ^ Fintype.card I)
    (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (xi_lt_one hq)).le) _)
    frameInverse_symmetric
  · intro s t
    simpa only [gram, frame_gram z hq] using frame_inverse (I := I) hq s t
  · intro s
    exact (frameInverse_abs_row hq s).le

/-- The literal sharp lower Gram factor `(1-xi)^n`, including `n = 0`. -/
theorem frame_energy_lower (z : V) (hq : 1 < Fintype.card V)
    (c : (I → Bool) → ℝ) :
    (1 - xi V) ^ Fintype.card I * (∑ s, c s ^ 2) ≤
      ∑ x : I → V, synthesize z c x ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (frame_coefficient_energy z hq c)
    (pow_nonneg (sub_pos.mpr (xi_lt_one hq)).le (Fintype.card I))
  have hcancel : (1 - xi V) ^ Fintype.card I *
      ((1 - xi V)⁻¹) ^ Fintype.card I = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (xi_lt_one hq))), one_pow]
  simpa only [← mul_assoc, hcancel, one_mul] using h

/-- Untouched residual labels retain the same factor for arbitrary joint data. -/
theorem frame_coefficient_family_energy {Y : Type*} [Fintype Y]
    (z : V) (hq : 1 < Fintype.card V) (c : Y → (I → Bool) → ℝ) :
    (∑ y, ∑ s, c y s ^ 2) ≤ ((1 - xi V)⁻¹) ^ Fintype.card I *
      ∑ y, ∑ x : I → V, synthesize z (c y) x ^ 2 := by
  calc
    _ ≤ ∑ y, ((1 - xi V)⁻¹) ^ Fintype.card I *
        ∑ x : I → V, synthesize z (c y) x ^ 2 :=
      Finset.sum_le_sum (fun y _ => frame_coefficient_energy z hq (c y))
    _ = _ := (Finset.mul_sum _ _ _).symm
end Tensor
end AES8.PaperActivityArrayFrame
