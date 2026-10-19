import AESPaper.ScalarActivityArrays

/-!
# Six scalar Boolean activity-choice array bounds
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.SimpleActivityArrays
open AESMixing AESPaper.RectangularFourier AESPaper.ScalarActivityArrays

def array33 (e : ℝ) : Choice 3 → Choice 3 → ℝ :=
  weightArray 3 3 (fun t => if t = 3 then e else 0)

def array31 (A B : ℝ) : Choice 3 → Choice 1 → ℝ :=
  weightArray 3 1 (interiorEntry A B)

def array30 (A B : ℝ) : Choice 3 → Choice 0 → ℝ :=
  weightArray 3 0 (endpointEntry 3 A B)

def array21 (A B : ℝ) : Choice 2 → Choice 1 → ℝ :=
  weightArray 2 1 (endpointEntry 3 A B)

def array20 (A B : ℝ) : Choice 2 → Choice 0 → ℝ :=
  weightArray 2 0 (endpointEntry 2 A B)

def array11 (A B : ℝ) : Choice 1 → Choice 1 → ℝ :=
  weightArray 1 1 (endpointEntry 2 A B)

theorem array33_nonnegative (e : ℝ) (he : 0 ≤ e) (s t : Choice 3) :
    0 ≤ array33 e s t := by
  unfold array33 weightArray
  dsimp only
  split_ifs <;> positivity

theorem array33_symmetric (e : ℝ) (s t : Choice 3) : array33 e s t = array33 e t s := by
  exact weightArray_swap 3 3 _ s t

theorem array33_row (e : ℝ) (he : 0 ≤ e) (s : Choice 3) :
    (∑ t : Choice 3, array33 e s t) ≤ 3 * e := by
  have hw : weight s ≤ 3 := weight_le s
  change (∑ t : Choice 3, (if weight s + weight t = 3 then e else 0)) ≤ 3 * e
  rw [sum_weight_three (fun k => if weight s + k = 3 then e else 0)]
  generalize hk : weight s = k at *
  interval_cases k <;> norm_num <;> linarith

theorem energyBound_array33 (e : ℝ) (he : 0 ≤ e) : EnergyBound (array33 e) (3 * e) := by
  apply energyBound_of_row_col (array33 e) (3 * e) (by positivity)
    (array33_nonnegative e he) (array33_row e he)
  intro t
  calc
    _ = ∑ s : Choice 3, array33 e t s :=
      Finset.sum_congr rfl (fun s _ => array33_symmetric e s t)
    _ ≤ 3 * e := array33_row e he t

/-- Exact column Gram of the (3,1) array. -/
theorem array31_gram (A B : ℝ) (s t : Choice 1) :
    gram (array31 A B) s t =
      if s 0 = t 0 then 4 * A ^ 2 + 3 * B ^ 2 else 6 * A * B := by
  change (∑ u : Choice 3, interiorEntry A B (weight u + weight s) *
      interiorEntry A B (weight u + weight t)) = _
  rw [sum_weight_three (fun k => interiorEntry A B (k + weight s) *
    interiorEntry A B (k + weight t))]
  rw [weight_one s, weight_one t]
  cases hs : s 0 <;> cases ht : t 0 <;>
    norm_num [interiorEntry, hs, ht] <;> ring

theorem array31_gram_row (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : Choice 1) :
    (∑ t : Choice 1, |gram (array31 A B) s t|) ≤
      4 * A ^ 2 + 6 * A * B + 3 * B ^ 2 := by
  have hD : 0 ≤ 4 * A ^ 2 + 3 * B ^ 2 := by positivity
  have hE : 0 ≤ 6 * A * B := by positivity
  rw [sum_choice_one]
  cases hs : s 0 <;>
    simp [array31_gram, hs, abs_of_nonneg hD, abs_of_nonneg hE] <;> nlinarith

theorem energyBound_array31 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (array31 A B) (Real.sqrt (4 * A ^ 2 + 6 * A * B + 3 * B ^ 2)) :=
  energyBound_of_gram_rows _ _ (by positivity) (array31_gram_row A B hA hB)

/-- The empty input activity index gives one Boolean choice, not zero columns. -/
theorem array30_gram (A B : ℝ) (s t : Choice 0) :
    gram (array30 A B) s t = 2 * A ^ 2 + 6 * B ^ 2 := by
  change (∑ u : Choice 3, endpointEntry 3 A B (weight u + weight s) *
      endpointEntry 3 A B (weight u + weight t)) = _
  rw [weight_zero s, weight_zero t]
  simp only [Nat.add_zero]
  rw [sum_weight_three (fun k => endpointEntry 3 A B k * endpointEntry 3 A B k)]
  norm_num [endpointEntry] <;> ring

theorem energyBound_array30 (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    EnergyBound (array30 A B) (Real.sqrt (2 * A ^ 2 + 6 * B ^ 2)) := by
  have hR : 0 ≤ 2 * A ^ 2 + 6 * B ^ 2 := by positivity
  apply energyBound_of_gram_rows _ _ hR
  intro s
  simp only [sum_choice_zero, array30_gram, abs_of_nonneg hR]
  exact le_rfl

/-- Exact column Gram of the (2,1) array. -/
theorem array21_gram (A B : ℝ) (s t : Choice 1) :
    gram (array21 A B) s t =
      if s 0 = t 0 then A ^ 2 + 3 * B ^ 2 else 2 * A * B + 2 * B ^ 2 := by
  change (∑ u : Choice 2, endpointEntry 3 A B (weight u + weight s) *
      endpointEntry 3 A B (weight u + weight t)) = _
  rw [sum_weight_two (fun k => endpointEntry 3 A B (k + weight s) *
    endpointEntry 3 A B (k + weight t))]
  rw [weight_one s, weight_one t]
  cases hs : s 0 <;> cases ht : t 0 <;>
    norm_num [endpointEntry, hs, ht] <;> ring

theorem array21_gram_row (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (s : Choice 1) :
    (∑ t : Choice 1, |gram (array21 A B) s t|) ≤ A ^ 2 + 2 * A * B + 5 * B ^ 2 := by
  have hD : 0 ≤ A ^ 2 + 3 * B ^ 2 := by positivity
  have hE : 0 ≤ 2 * A * B + 2 * B ^ 2 := by positivity
  rw [sum_choice_one]
  cases hs : s 0 <;>
    simp [array21_gram, hs, abs_of_nonneg hD, abs_of_nonneg hE] <;> nlinarith

theorem energyBound_array21 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (array21 A B) (Real.sqrt (A ^ 2 + 2 * A * B + 5 * B ^ 2)) :=
  energyBound_of_gram_rows _ _ (by positivity) (array21_gram_row A B hA hB)

theorem array20_gram (A B : ℝ) (s t : Choice 0) :
    gram (array20 A B) s t = 2 * A ^ 2 + 2 * B ^ 2 := by
  change (∑ u : Choice 2, endpointEntry 2 A B (weight u + weight s) *
      endpointEntry 2 A B (weight u + weight t)) = _
  rw [weight_zero s, weight_zero t]
  simp only [Nat.add_zero]
  rw [sum_weight_two (fun k => endpointEntry 2 A B k * endpointEntry 2 A B k)]
  norm_num [endpointEntry] <;> ring

theorem energyBound_array20 (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    EnergyBound (array20 A B) (Real.sqrt (2 * A ^ 2 + 2 * B ^ 2)) := by
  have hR : 0 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by positivity
  apply energyBound_of_gram_rows _ _ hR
  intro s
  simp only [sum_choice_zero, array20_gram, abs_of_nonneg hR]
  exact le_rfl

theorem array11_nonnegative (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s t : Choice 1) : 0 ≤ array11 A B s t :=
  endpointEntry_nonnegative 2 A B hA hB _

theorem array11_symmetric (A B : ℝ) (s t : Choice 1) :
    array11 A B s t = array11 A B t s := weightArray_swap 1 1 _ s t

theorem array11_row (A B : ℝ) (s : Choice 1) :
    (∑ t : Choice 1, array11 A B s t) = A + B := by
  change (∑ t : Choice 1, endpointEntry 2 A B (weight s + weight t)) = A + B
  rw [sum_weight_one (fun k => endpointEntry 2 A B (weight s + k)), weight_one s]
  cases hs : s 0 <;> norm_num [endpointEntry, hs] <;> ring

theorem energyBound_array11 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (array11 A B) (A + B) := by
  apply energyBound_of_row_col (array11 A B) (A + B) (by positivity)
    (array11_nonnegative A B hA hB) (fun s => (array11_row A B s).le)
  intro t
  calc
    _ = ∑ s : Choice 1, array11 A B t s :=
      Finset.sum_congr rfl (fun s _ => array11_symmetric A B s t)
    _ ≤ A + B := (array11_row A B t).le

end AESPaper.SimpleActivityArrays
