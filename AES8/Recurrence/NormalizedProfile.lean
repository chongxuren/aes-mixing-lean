/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.SupportOutput
import AES8.Consequences.ConcreteBridge

/-!
# Normalized profiles of the actual grouped AES error

The profile is constructed from the concrete error at round `4+2*j`.
The factor `2^80` is exactly `q^(5/2)` for the word alphabet `q=2^32`.
Its output inequality follows from the support-sensitive distance conversion;
it is not an additional hypothesis of the remaining analytic interface.
Startup and the first/later return estimates remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section

namespace AES8.NormalizedProfile
open AESMixing AESMixing.AES

theorem diagonal_pos (i : Fin 14) : 0 < d i := by
  fin_cases i <;> norm_num [d, vec14_apply]

/-- Remove the expected two-round decay and the four-round scale. -/
def factor (j : ℕ) : ℝ := (2 : ℝ) ^ (80 : ℕ) / omega41 ^ j

theorem factor_pos (j : ℕ) : 0 < factor j :=
  div_pos (by positivity) (pow_pos omega41_pos j)

/-- The actual normalized profile, rather than an unspecified witness. -/
def actual (a : AES.State) (j : ℕ) : Profile :=
  fun i => factor j * SupportProfile.actual a j i / d i

theorem actual_nonneg (a : AES.State) (j : ℕ) (i : Fin 14) :
    0 ≤ actual a j i :=
  div_nonneg
    (mul_nonneg (factor_pos j).le (SupportProfile.actual_nonneg a j i))
    (diagonal_pos i).le

theorem physical_actual (a : AES.State) (j : ℕ) :
    physical (actual a j) = scale (factor j) (SupportProfile.actual a j) := by
  funext i
  have hd : d i ≠ 0 := (diagonal_pos i).ne'
  simp only [physical, actual, scale]
  field_simp [hd]

theorem Phi_actual (a : AES.State) (j : ℕ) :
    Phi (actual a j) = factor j * SupportOutput.psi (SupportProfile.actual a j) := by
  rw [← SupportOutput.psi_physical, physical_actual,
    SupportOutput.psi_scale _ _ (factor_pos j).le]

theorem factor_cancellation (j : ℕ) :
    (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ j * factor j = (2 : ℝ) ^ (63 : ℕ) := by
  have hw : omega41 ^ j ≠ 0 := (pow_pos omega41_pos j).ne'
  unfold factor
  field_simp [hw]

/-- The profile-to-TV estimate is proved for every actual nonzero difference. -/
theorem output (a : AES.State) (ha : a ≠ 0) (j : ℕ) :
    tv (physicalDifferenceLaw (4 + 2 * j) a) (uniformExcept (0 : AES.State)) ≤
      (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ j * Phi (actual a j) := by
  rw [ConcreteBridge.grouped_error_tv]
  have h := SupportOutput.support_sensitive_tv (AESPaper.GroupedLaw.error (j + 1) a)
    (AESPaper.GroupedLaw.error_zero (j + 1) a ha)
    (AESPaper.GroupedLaw.error_sum (j + 1) a)
  change _ ≤ (2 : ℝ) ^ (63 : ℕ) * SupportOutput.psi (SupportProfile.actual a j) at h
  rw [Phi_actual, ← _root_.mul_assoc, factor_cancellation]
  exact h

/-- Only the concrete startup and transfer/return estimates remain here.
Nonnegativity and output conversion have already been proved for `actual`. -/
structure Estimates : Prop where
  initial : ∀ a : AES.State, a ≠ 0 → actual a 0 ≤ scale 1000 u0
  first : ∀ a : AES.State, a ≠ 0 →
    actual a 1 ≤ fun i => L (actual a 0) i + 1000 * g i
  step : ∀ a : AES.State, a ≠ 0 → ∀ j : ℕ,
    actual a (j + 2) ≤ fun i => L (actual a (j + 1)) i + M (actual a j) i

theorem differenceProfileBounds (h : Estimates) :
    ConcreteBridge.DifferenceProfileBounds actual := by
  intro a ha
  exact {
    nonnegative := actual_nonneg a
    initial := h.initial a ha
    first := h.first a ha
    step := h.step a ha
    output := output a ha
  }

/-- This final implication still requires the three concrete estimates above. -/
theorem epsilon_eight_plus_two (h : Estimates) (k : ℕ) :
    AES.epsilon (8 + 2 * k) < ConcreteBridge.dyadicBound k :=
  ConcreteBridge.epsilon_eight_plus_two (differenceProfileBounds h) k

end AES8.NormalizedProfile
