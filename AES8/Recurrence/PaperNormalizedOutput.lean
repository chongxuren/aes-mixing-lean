import AES8.Reductions.Support.PaperPhysicalOutput
import AES8.Recurrence.NormalizedProfile

/-!
# Current output conversion for the actual normalized AES profile

The physical profile, diagonal, grouped error and normalization are shared with
the historical route. Only the current quadrature functional is used below.
No recurrence, initialization, envelope membership or final mixing estimate is
assumed by this output conversion.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperNormalizedOutput
open AESMixing AESMixing.AES

/-- Positive homogeneity includes every support-wise Euclidean norm. -/
theorem psi_scale (a : ℝ) (v : Profile) (ha : 0 ≤ a) :
    PaperPhysicalOutput.psi (scale a v) = a * PaperPhysicalOutput.psi v := by
  have h1 : (a * v 4) ^ 2 = a ^ 2 * (v 4 ^ 2) := by ring
  have h2 : (a * v 5) ^ 2 + (a * v 8) ^ 2 = a ^ 2 * (v 5 ^ 2 + v 8 ^ 2) := by ring
  have h3 : (a * v 6) ^ 2 + (a * v 9) ^ 2 + (a * v 11) ^ 2 =
      a ^ 2 * (v 6 ^ 2 + v 9 ^ 2 + v 11 ^ 2) := by ring
  have h4 : (a * v 7) ^ 2 + (a * v 10) ^ 2 + (a * v 12) ^ 2 + (a * v 13) ^ 2 =
      a ^ 2 * (v 7 ^ 2 + v 10 ^ 2 + v 12 ^ 2 + v 13 ^ 2) := by ring
  unfold PaperPhysicalOutput.psi scale
  rw [h1, h2, h3, h4]
  simp only [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

theorem Phi_actual (a : AES.State) (j : ℕ) :
    PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) =
      NormalizedProfile.factor j * PaperPhysicalOutput.psi (SupportProfile.actual a j) := by
  unfold PaperPhysicalOutput.Phi
  rw [NormalizedProfile.physical_actual,
    psi_scale _ _ (NormalizedProfile.factor_pos j).le]

/-- The output clause of the paper's normalized-profile proposition for its
literal centered error and current functional. This is unconditional. -/
theorem actual_output (a : AES.State) (ha : a ≠ 0) (j : ℕ) :
    tv (physicalDifferenceLaw (4 + 2 * j) a) (uniformExcept (0 : AES.State)) ≤
      (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ j *
        PaperPhysicalOutput.Phi (NormalizedProfile.actual a j) := by
  rw [ConcreteBridge.grouped_error_tv]
  have h := PaperPhysicalOutput.support_sensitive_tv (AESPaper.GroupedLaw.error (j + 1) a)
    (AESPaper.GroupedLaw.error_zero (j + 1) a ha)
    (AESPaper.GroupedLaw.error_sum (j + 1) a)
  change _ ≤ (2 : ℝ) ^ (63 : ℕ) * PaperPhysicalOutput.psi (SupportProfile.actual a j) at h
  rw [Phi_actual, ← _root_.mul_assoc, NormalizedProfile.factor_cancellation]
  exact h

end AES8.PaperNormalizedOutput
