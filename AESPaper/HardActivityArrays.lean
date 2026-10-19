import AESPaper.ScalarActivityArrays
import AESMixing.MatrixEstimate
import AESMixing.WeightedRectangularSchur

/-!
# The two harder finite scalar activity arrays

The Boolean-choice arrays use their actual Hamming-weight entry rules.
Positive-vector Schur certificates prove upper energy bounds for every
signed input. The (2,2) boundary A=0 is treated separately, since the
interior positive witness would otherwise have zero coordinates. The
(3,2) certificate is proved for the normalized array and then scaled by e,
so e=0 is included. All coefficients are raw, before frame or q^2 factors.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.HardActivityArrays
open AESMixing
open AESPaper.ScalarActivityArrays
open AESPaper.RectangularFourier (EnergyBound)

def array22 (A B : ℝ) : Choice 2 → Choice 2 → ℝ :=
  weightArray 2 2 (interiorEntry A B)

def lambda22 (A B : ℝ) : ℝ := (3 * B + Real.sqrt (B ^ 2 + 16 * A ^ 2)) / 2

theorem lambda22_nonnegative (A B : ℝ) (hB : 0 ≤ B) : 0 ≤ lambda22 A B := by
  unfold lambda22
  positivity

theorem lambda22_polynomial (A B : ℝ) :
    lambda22 A B ^ 2 - 3 * B * lambda22 A B + 2 * B ^ 2 - 4 * A ^ 2 = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 16 * A ^ 2 by positivity)
  unfold lambda22
  nlinarith

theorem lambda22_zero (B : ℝ) (hB : 0 ≤ B) : lambda22 0 B = 2 * B := by
  unfold lambda22
  rw [show B ^ 2 + 16 * (0 : ℝ) ^ 2 = B ^ 2 by ring, Real.sqrt_sq hB]
  ring

theorem array22_nonnegative (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s t : Choice 2) : 0 ≤ array22 A B s t := by
  unfold array22 weightArray interiorEntry
  split_ifs <;> positivity

theorem array22_symmetric (A B : ℝ) (s t : Choice 2) :
    array22 A B s t = array22 A B t s := by
  unfold array22 weightArray
  rw [Nat.add_comm]

/-- A Hamming-weight form of the exact positive eigenvector. -/
def vector22 (A B : ℝ) (k : ℕ) : ℝ :=
  if k = 1 then lambda22 A B - B else 2 * A

theorem vector22_positive (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (k : ℕ) :
    0 < vector22 A B k := by
  unfold vector22
  split_ifs
  · have hs : 0 < Real.sqrt (B ^ 2 + 16 * A ^ 2) := Real.sqrt_pos.mpr (by positivity)
    unfold lambda22
    linarith
  · positivity

/-- Exact row certificate on the actual Boolean-choice array. -/
theorem array22_weighted_row (A B : ℝ) (s : Choice 2) :
    (∑ t : Choice 2, array22 A B s t * vector22 A B (weight t)) =
      lambda22 A B * vector22 A B (weight s) := by
  change (∑ t : Choice 2,
    interiorEntry A B (weight s + weight t) * vector22 A B (weight t)) = _
  rw [sum_weight_two (fun k => interiorEntry A B (weight s + k) * vector22 A B k)]
  have hw := weight_le s
  interval_cases h : weight s <;>
    norm_num [interiorEntry, vector22, h] <;> nlinarith [lambda22_polynomial A B]

/-- A=0 uses the strictly positive constant witness, including B=0. -/
theorem array22_zero_row (B : ℝ) (hB : 0 ≤ B) (s : Choice 2) :
    (∑ t : Choice 2, array22 0 B s t * (1 : ℝ)) ≤ (2 * B) * 1 := by
  change (∑ t : Choice 2, interiorEntry 0 B (weight s + weight t) * (1 : ℝ)) ≤ _
  rw [sum_weight_two (fun k => interiorEntry 0 B (weight s + k) * (1 : ℝ))]
  have hw := weight_le s
  interval_cases h : weight s <;> norm_num [interiorEntry, h] <;> nlinarith

theorem energyBound_array22 (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    EnergyBound (array22 A B) (lambda22 A B) := by
  by_cases hz : A = 0
  · subst A
    rw [lambda22_zero B hB]
    intro f
    exact weighted_schur_energy (array22 0 B) (fun _ => 1) (2 * B)
      (by positivity) (array22_nonnegative 0 B (by norm_num) hB)
      (array22_symmetric 0 B) (fun _ => by norm_num) (array22_zero_row B hB) f
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    intro f
    exact weighted_schur_energy (array22 A B) (fun s => vector22 A B (weight s))
      (lambda22 A B) (lambda22_nonnegative A B hB) (array22_nonnegative A B hA hB)
      (array22_symmetric A B) (fun s => vector22_positive A B hp hB (weight s))
      (fun s => (array22_weighted_row A B s).le) f

def entry32 (e : ℝ) (k : ℕ) : ℝ := if k = 2 ∨ k = 3 then e else 0

def array32 (e : ℝ) : Choice 3 → Choice 2 → ℝ := weightArray 3 2 (entry32 e)

def rho32 : ℝ := 8 + 2 * Real.sqrt 13
def coefficient32 : ℝ := Real.sqrt rho32

theorem rho32_positive : 0 < rho32 := by
  unfold rho32
  positivity

theorem coefficient32_positive : 0 < coefficient32 := Real.sqrt_pos.mpr rho32_positive

theorem coefficient32_sq : coefficient32 ^ 2 = rho32 := Real.sq_sqrt rho32_positive.le

theorem array32_nonnegative (e : ℝ) (he : 0 ≤ e) (s : Choice 3) (t : Choice 2) :
    0 ≤ array32 e s t := by
  unfold array32 weightArray entry32
  split_ifs <;> positivity

theorem array32_scale (e : ℝ) : array32 e = fun s t => e * array32 1 s t := by
  funext s t
  unfold array32 weightArray entry32
  split_ifs <;> simp

def vector32 (k : ℕ) : ℝ := if k = 1 then 2 + Real.sqrt 13 else 3

def rowNumerator32 (k : ℕ) : ℝ :=
  if k = 0 ∨ k = 3 then 3 else 7 + 2 * Real.sqrt 13

def inputWitness32 (t : Choice 2) : ℝ := vector32 (weight t)
def outputWitness32 (s : Choice 3) : ℝ := rowNumerator32 (weight s) / coefficient32

theorem inputWitness32_positive (t : Choice 2) : 0 < inputWitness32 t := by
  unfold inputWitness32 vector32
  split_ifs <;> positivity

theorem outputWitness32_positive (s : Choice 3) : 0 < outputWitness32 s := by
  apply div_pos _ coefficient32_positive
  unfold rowNumerator32
  split_ifs <;> positivity

/-- These exact finite weighted sums certify the actual normalized matrix;
no manuscript eigenvalue assertion is used as a premise. -/
theorem array32_normalized_row (s : Choice 3) :
    (∑ t : Choice 2, array32 1 s t * vector32 (weight t)) = rowNumerator32 (weight s) := by
  change (∑ t : Choice 2, entry32 1 (weight s + weight t) * vector32 (weight t)) = _
  rw [sum_weight_two (fun k => entry32 1 (weight s + k) * vector32 k)]
  have hw := weight_le s
  interval_cases h : weight s <;>
    norm_num [entry32, vector32, rowNumerator32, h] <;> ring

theorem array32_normalized_column (t : Choice 2) :
    (∑ s : Choice 3, array32 1 s t * rowNumerator32 (weight s)) =
      rho32 * vector32 (weight t) := by
  change (∑ s : Choice 3,
    entry32 1 (weight s + weight t) * rowNumerator32 (weight s)) = _
  rw [sum_weight_three (fun k => entry32 1 (k + weight t) * rowNumerator32 k)]
  have hw := weight_le t
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  interval_cases h : weight t <;>
    norm_num [entry32, vector32, rowNumerator32, rho32, h] <;> nlinarith

theorem array32_weighted_row (s : Choice 3) :
    (∑ t : Choice 2, array32 1 s t * inputWitness32 t) =
      coefficient32 * outputWitness32 s := by
  change (∑ t : Choice 2, array32 1 s t * vector32 (weight t)) =
    coefficient32 * (rowNumerator32 (weight s) / coefficient32)
  rw [array32_normalized_row]
  field_simp [ne_of_gt coefficient32_positive]
  <;> ring

theorem array32_weighted_column (t : Choice 2) :
    (∑ s : Choice 3, array32 1 s t * outputWitness32 s) =
      coefficient32 * inputWitness32 t := by
  change (∑ s : Choice 3,
    array32 1 s t * (rowNumerator32 (weight s) / coefficient32)) =
      coefficient32 * vector32 (weight t)
  calc
    _ = (∑ s : Choice 3, array32 1 s t * rowNumerator32 (weight s)) / coefficient32 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = (rho32 * vector32 (weight t)) / coefficient32 := by rw [array32_normalized_column]
    _ = _ := by
      rw [← coefficient32_sq]
      field_simp [ne_of_gt coefficient32_positive]
      <;> ring

theorem energyBound_array32_one : EnergyBound (array32 1) coefficient32 := by
  intro f
  exact weighted_rectangular_schur_energy (array32 1) outputWitness32 inputWitness32 coefficient32
    coefficient32_positive.le (array32_nonnegative 1 (by norm_num))
    outputWitness32_positive inputWitness32_positive
    (fun s => (array32_weighted_row s).le) (fun t => (array32_weighted_column t).le) f

theorem array32_coefficient_nonnegative (e : ℝ) (he : 0 ≤ e) : 0 ≤ e * coefficient32 :=
  mul_nonneg he coefficient32_positive.le

theorem array32_coefficient_sq (e : ℝ) :
    (e * coefficient32) ^ 2 = (8 + 2 * Real.sqrt 13) * e ^ 2 := by
  rw [mul_pow, coefficient32_sq]
  unfold rho32
  ring

/-- The coefficient e*sqrt(8+2*sqrt(13)) includes the e=0 boundary. -/
theorem energyBound_array32 (e : ℝ) (_he : 0 ≤ e) :
    EnergyBound (array32 e) (e * coefficient32) := by
  rw [array32_scale]
  exact AESPaper.RectangularBounds.energyBound_scale e _ _ energyBound_array32_one

end AESPaper.HardActivityArrays
