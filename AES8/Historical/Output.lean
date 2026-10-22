/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.Data

/-!
# The output functional for the fourteen-coordinate recurrence

The weighted coordinates here use the exact rational diagonal `d` in `Data`.
The square-root comparison follows the nonnegative-coordinate argument in
`AESRound.Terminal.blockNorm_mono`; the present functional has its own linear
part and only four coordinates in its norm term.

These are analytic and rational-arithmetic lemmas.  The link to an AES error
sequence is supplied separately, and no cryptanalytic experiment is performed.
-/

noncomputable section

namespace AES8

/-- Undo the diagonal normalization of a recurrence profile. -/
def physical (z : Profile) : Profile := fun i => d i * z i

/-- The linear part of the output estimate, before its four-coordinate norm. -/
def outputLinear (z : Profile) : ℝ :=
  2 * (physical z 0 / 2 ^ (47 : ℕ) +
      5 * physical z 1 / 2 ^ (33 : ℕ) +
      physical z 2 / 2 ^ (15 : ℕ)) +
    physical z 4 / 2 ^ (47 : ℕ) +
    5 * (physical z 5 + physical z 8) / 2 ^ (33 : ℕ) +
    (physical z 6 + physical z 9 + physical z 11) / 2 ^ (15 : ℕ)

/-- The squared norm in the output estimate. -/
def outputSquared (z : Profile) : ℝ :=
  (physical z 7) ^ 2 + (physical z 10) ^ 2 +
    (physical z 12) ^ 2 + (physical z 13) ^ 2

/-- Output estimate in normalized recurrence coordinates. -/
def Phi (z : Profile) : ℝ :=
  outputLinear z + Real.sqrt (outputSquared z)

private theorem output_d_nonneg (i : Fin 14) : 0 ≤ d i := by
  fin_cases i <;> norm_num [d]

theorem physical_nonneg {z : Profile} (hz : ∀ i, 0 ≤ z i) :
    ∀ i, 0 ≤ physical z i := by
  intro i
  exact mul_nonneg (output_d_nonneg i) (hz i)

theorem physical_mono {x y : Profile} (hxy : ∀ i, x i ≤ y i) :
    ∀ i, physical x i ≤ physical y i := by
  intro i
  exact mul_le_mul_of_nonneg_left (hxy i) (output_d_nonneg i)

theorem outputLinear_mono {x y : Profile} (hxy : ∀ i, x i ≤ y i) :
    outputLinear x ≤ outputLinear y := by
  have hw := physical_mono hxy
  norm_num only [outputLinear]
  linarith [hw 0, hw 1, hw 2, hw 4, hw 5, hw 6, hw 8, hw 9, hw 11]

private theorem nonneg_square_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  have hp : 0 ≤ (b - a) * (b + a) :=
    mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  nlinarith [hp]

theorem outputSquared_mono {x y : Profile} (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) : outputSquared x ≤ outputSquared y := by
  have hxw := physical_nonneg hx
  have hxyw := physical_mono hxy
  have h7 := nonneg_square_mono (hxw 7) (hxyw 7)
  have h10 := nonneg_square_mono (hxw 10) (hxyw 10)
  have h12 := nonneg_square_mono (hxw 12) (hxyw 12)
  have h13 := nonneg_square_mono (hxw 13) (hxyw 13)
  unfold outputSquared
  linarith

/-- The output functional is monotone on nonnegative recurrence profiles. -/
theorem Phi_mono {x y : Profile} (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) : Phi x ≤ Phi y := by
  exact add_le_add (outputLinear_mono hxy)
    (Real.sqrt_le_sqrt (outputSquared_mono hx hxy))

theorem Phi_monotoneOn_nonnegative :
    MonotoneOn Phi {x : Profile | ∀ i, 0 ≤ x i} := by
  intro x hx y _ hxy
  exact Phi_mono hx hxy

theorem outputLinear_scale (a : ℝ) (z : Profile) :
    outputLinear (scale a z) = a * outputLinear z := by
  unfold outputLinear physical scale
  ring

theorem outputSquared_scale (a : ℝ) (z : Profile) :
    outputSquared (scale a z) = a ^ 2 * outputSquared z := by
  unfold outputSquared physical scale
  ring

/-- Nonnegative homogeneity is used when propagating the recurrence envelope. -/
theorem Phi_scale (a : ℝ) (z : Profile) (ha : 0 ≤ a) :
    Phi (scale a z) = a * Phi z := by
  unfold Phi
  rw [outputLinear_scale, outputSquared_scale,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

/-- A reusable conversion from rational squared bounds to a strict output cap. -/
theorem Phi_lt_of_linear_sq_bounds {z : Profile} {l r b : ℝ}
    (hr : 0 ≤ r) (hlinear : outputLinear z < l)
    (hsquared : outputSquared z ≤ r ^ 2) (hcap : l + r ≤ b) :
    Phi z < b := by
  have hnorm : Real.sqrt (outputSquared z) ≤ r := by
    calc
      Real.sqrt (outputSquared z) ≤ Real.sqrt (r ^ 2) :=
        Real.sqrt_le_sqrt hsquared
      _ = r := Real.sqrt_sq hr
  unfold Phi
  linarith

/- The loose integer caps deliberately leave rational slack, so no numerical
   approximation of a square root occurs in either concrete certificate. -/

theorem outputLinear_1000_u2_lt : outputLinear (scale 1000 u2) < 1 := by
  norm_num [outputLinear, physical, scale, d, u2, vec14_apply]

theorem outputSquared_1000_u2_le : outputSquared (scale 1000 u2) ≤ (31 : ℝ) ^ 2 := by
  norm_num [outputSquared, physical, scale, d, u2, vec14_apply]

theorem Phi_1000_u2_lt : Phi (scale 1000 u2) < 32 := by
  exact Phi_lt_of_linear_sq_bounds (l := 1) (r := 31)
    (by norm_num) outputLinear_1000_u2_lt
    outputSquared_1000_u2_le (by norm_num)

theorem outputLinear_10000_h_lt : outputLinear (scale 10000 h) < 2 := by
  norm_num [outputLinear, physical, scale, d, h, vec14_apply]

theorem outputSquared_10000_h_le : outputSquared (scale 10000 h) ≤ (126 : ℝ) ^ 2 := by
  norm_num [outputSquared, physical, scale, d, h, vec14_apply]

theorem Phi_10000_h_lt : Phi (scale 10000 h) < 128 := by
  exact Phi_lt_of_linear_sq_bounds (l := 2) (r := 126)
    (by norm_num) outputLinear_10000_h_lt
    outputSquared_10000_h_le (by norm_num)

end AES8
