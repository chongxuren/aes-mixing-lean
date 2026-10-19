import AESPaper.ScalarActivityArrays
import AESPaper.HardActivityArrays
import AESPaper.WordPhysicalEnergy

/-!
# Scalar activity-input arrays with four input choices

These counting-measure bounds hold for every real signed input vector.
The (2,4) and (1,4) arrays are estimated through the actual row Grams,
using scalar transposition only. The (0,4) array has one row: Choice 0
contains its unique empty Boolean tuple. Physical per-choice bounds,
both frame factors, position aggregation and b rounding are separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActivityInputArrays
open AESMixing
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.ScalarActivityArrays

/-- Exact four-coordinate Boolean weight multiplicities. -/
theorem sum_weight_four (f : ℕ → ℝ) :
    (∑ s : Choice 4, f (weight s)) =
      f 0 + 4 * f 1 + 6 * f 2 + 4 * f 3 + f 4 := by
  calc
    _ = (∑ s : Choice 3, f (weight s)) +
        ∑ s : Choice 3, f (1 + weight s) := by
      rw [sum_choice_succ 3]
      simp [weight_cons]
    _ = _ := by
      rw [sum_weight_three f, sum_weight_three (fun k => f (1 + k))]
      norm_num <;> ring

def array24 (e : ℝ) : Choice 2 → Choice 4 → ℝ :=
  weightArray 2 4 (fun k => if k = 3 then e else 0)

def array14 (e : ℝ) : Choice 1 → Choice 4 → ℝ :=
  weightArray 1 4 (HardActivityArrays.entry32 e)

def array04 (A B : ℝ) : Choice 0 → Choice 4 → ℝ :=
  weightArray 0 4 (interiorEntry A B)

theorem array24_nonnegative (e : ℝ) (he : 0 ≤ e)
    (s : Choice 2) (t : Choice 4) : 0 ≤ array24 e s t := by
  dsimp only [array24, weightArray]
  split_ifs <;> positivity

theorem array14_nonnegative (e : ℝ) (he : 0 ≤ e)
    (s : Choice 1) (t : Choice 4) : 0 ≤ array14 e s t := by
  unfold array14 weightArray HardActivityArrays.entry32
  split_ifs <;> positivity

theorem array04_nonnegative (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s : Choice 0) (t : Choice 4) : 0 ≤ array04 A B s t :=
  interiorEntry_nonnegative A B hA hB _

/-- Different row weights have disjoint support. The two weight-one rows
coincide, with six entries; the remaining two row squares have four. -/
theorem array24_transpose_gram (e : ℝ) (s t : Choice 2) :
    gram (RectangularBounds.transpose (array24 e)) s t =
      if weight s = weight t then
        (if weight s = 1 then 6 else 4) * e ^ 2
      else 0 := by
  change (∑ u : Choice 4,
    (if weight s + weight u = 3 then e else 0) *
      (if weight t + weight u = 3 then e else 0)) = _
  rw [sum_weight_four (fun k =>
    (if weight s + k = 3 then e else 0) *
      (if weight t + k = 3 then e else 0))]
  have hws : weight s ≤ 2 := weight_le s
  have hwt : weight t ≤ 2 := weight_le t
  generalize hs : weight s = a at *
  generalize ht : weight t = b at *
  interval_cases a <;> interval_cases b <;> norm_num <;> ring

theorem array24_transpose_gram_row (e : ℝ) (s : Choice 2) :
    (∑ t : Choice 2, |gram (RectangularBounds.transpose (array24 e)) s t|) ≤
      12 * e ^ 2 := by
  have h4 : 0 ≤ 4 * e ^ 2 := by positivity
  have h6 : 0 ≤ 6 * e ^ 2 := by positivity
  have hws : weight s ≤ 2 := weight_le s
  simp only [array24_transpose_gram]
  rw [sum_weight_two (fun k =>
    |if weight s = k then (if weight s = 1 then 6 else 4) * e ^ 2 else 0|)]
  generalize hs : weight s = a at *
  interval_cases a <;>
    norm_num [abs_of_nonneg h4, abs_of_nonneg h6] <;> nlinarith [sq_nonneg e]

/-- The exact squared cap is 12*e^2. -/
theorem energyBound_array24 (e : ℝ) (he : 0 ≤ e) :
    EnergyBound (array24 e) (Real.sqrt 12 * e) := by
  have hg : EnergyBound (RectangularBounds.transpose (array24 e))
      (Real.sqrt (12 * e ^ 2)) :=
    energyBound_of_gram_rows _ _ (by positivity) (array24_transpose_gram_row e)
  have h : EnergyBound (array24 e) (Real.sqrt (12 * e ^ 2)) :=
    (RectangularBounds.energyBound_transpose_iff (array24 e) _).mp hg
  have hc : Real.sqrt (12 * e ^ 2) = Real.sqrt 12 * e := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) he)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  rw [hc] at h
  exact h

/-- The actual two-row Gram is e^2 times [[10,6],[6,10]]. -/
theorem array14_transpose_gram (e : ℝ) (s t : Choice 1) :
    gram (RectangularBounds.transpose (array14 e)) s t =
      if s 0 = t 0 then 10 * e ^ 2 else 6 * e ^ 2 := by
  change (∑ u : Choice 4,
    HardActivityArrays.entry32 e (weight s + weight u) *
      HardActivityArrays.entry32 e (weight t + weight u)) = _
  rw [sum_weight_four (fun k =>
    HardActivityArrays.entry32 e (weight s + k) *
      HardActivityArrays.entry32 e (weight t + k))]
  rw [weight_one s, weight_one t]
  cases hs : s 0 <;> cases ht : t 0 <;>
    norm_num [HardActivityArrays.entry32, hs, ht] <;> ring

theorem array14_transpose_gram_row (e : ℝ) (s : Choice 1) :
    (∑ t : Choice 1, |gram (RectangularBounds.transpose (array14 e)) s t|) ≤
      16 * e ^ 2 := by
  have hD : 0 ≤ 10 * e ^ 2 := by positivity
  have hE : 0 ≤ 6 * e ^ 2 := by positivity
  rw [sum_choice_one]
  cases hs : s 0 <;>
    simp [array14_transpose_gram, hs, abs_of_nonneg hD, abs_of_nonneg hE] <;>
      nlinarith

/-- The exact squared cap is 16*e^2. -/
theorem energyBound_array14 (e : ℝ) (he : 0 ≤ e) :
    EnergyBound (array14 e) (4 * e) := by
  have hg : EnergyBound (RectangularBounds.transpose (array14 e))
      (Real.sqrt (16 * e ^ 2)) :=
    energyBound_of_gram_rows _ _ (by positivity) (array14_transpose_gram_row e)
  have h : EnergyBound (array14 e) (Real.sqrt (16 * e ^ 2)) :=
    (RectangularBounds.energyBound_transpose_iff (array14 e) _).mp hg
  have hc : Real.sqrt (16 * e ^ 2) = 4 * e := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) he)).mp
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [hc] at h
  exact h

/-- The unique row has eight line entries, six middle entries, and two zeros. -/
theorem array04_frobenius (A B : ℝ) :
    (∑ s : Choice 0, ∑ t : Choice 4, array04 A B s t ^ 2) =
      8 * A ^ 2 + 6 * B ^ 2 := by
  change (∑ s : Choice 0, ∑ t : Choice 4,
    interiorEntry A B (weight s + weight t) ^ 2) = _
  simp only [sum_choice_zero, weight_zero, Nat.zero_add]
  rw [sum_weight_four (fun k => interiorEntry A B k ^ 2)]
  norm_num [interiorEntry] <;> ring

theorem energyBound_array04 (A B : ℝ) :
    EnergyBound (array04 A B) (Real.sqrt (8 * A ^ 2 + 6 * B ^ 2)) := by
  apply WordPhysicalEnergy.energyBound_of_frobenius
  rw [array04_frobenius, Real.sq_sqrt (by positivity)]

end AESPaper.ActivityInputArrays
