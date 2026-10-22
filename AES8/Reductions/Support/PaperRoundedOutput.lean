import AES8.Reductions.Support.PaperSupportQuadrature
import AES8.Model.SupportProfile

/-!
# The current four-word output functional

This is the literal quadrature functional in frozen paper f902bb94,
`eq:output-functional`, with its four rounded weights. The exact generic
support conversion supplies the centered-error theorem; only four fixed
square-root comparisons are needed here. No recurrence estimate is assumed.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRoundedOutput
open AESMixing AESPaper.RareActivity
open PaperSupportOutput (supportRadius supportWeight ambientRadius)
open PaperSupportProjection (NonzeroState nonzeroProfile)

def weight (t : ℕ) : ℝ :=
  if t = 1 then 1 / 2 ^ (47 : ℕ) else
  if t = 2 then 5 / 2 ^ (33 : ℕ) else
  if t = 3 then 1 / 2 ^ (15 : ℕ) else 1

/-- Rounded four-word functional, with quadrature at every support size. -/
def psi (p : PaperSupportOutput.Profile) : ℝ :=
  2 * (∑ t : Fin 3, weight (t.val + 1) * p 0 (t.val + 1)) +
    ∑ t : Fin 4, weight (t.val + 1) *
      Real.sqrt (∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1) ^ 2)

theorem ambientRadius_four : ambientRadius 4 4294967296 = (2 : ℝ) ^ (64 : ℕ) := by
  unfold ambientRadius
  rw [show ((4294967296 : ℕ) : ℝ) ^ 4 = ((2 : ℝ) ^ (64 : ℕ)) ^ 2 by norm_num,
    Real.sqrt_sq (by positivity)]

theorem supportWeight_le (t : Fin 4) :
    supportWeight 4 4294967296 (t.val + 1) ≤ weight (t.val + 1) := by
  rw [supportWeight, ambientRadius_four, div_le_iff₀ (by positivity)]
  fin_cases t <;> norm_num [supportRadius, weight, Real.sqrt_le_iff, Nat.choose]

theorem exact_le_rounded (p : PaperSupportOutput.Profile) (hp : ∀ i t, 0 ≤ p i t) :
    PaperSupportQuadrature.psi 4 4294967296 p ≤ psi p := by
  unfold PaperSupportQuadrature.psi psi
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_right
      (supportWeight_le ⟨t.val, by omega⟩) (hp _ _)
  · exact Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_right (supportWeight_le t) (Real.sqrt_nonneg _))

/-- The paper's distance conversion for every centered real error on the
actual nonzero four-word AES domain. -/
theorem support_sensitive_distance
    (f : NonzeroState (0 : AES.Word) 4 → ℝ) (hcenter : (∑ x, f x) = 0) :
    l1 f / 2 ≤ (2 : ℝ) ^ (63 : ℕ) * psi (nonzeroProfile (0 : AES.Word) f) := by
  have h := PaperSupportQuadrature.support_sensitive_distance_nonzero
    (by norm_num : 1 ≤ 4) (0 : AES.Word) SupportProfile.word_card_gt_one f hcenter
  rw [AES.word_card, show (2 : ℕ) ^ 32 = 4294967296 by norm_num,
    ambientRadius_four] at h
  have hp : ∀ i t, 0 ≤ nonzeroProfile (0 : AES.Word) f i t := fun _ _ => l2_nonneg _
  have he := exact_le_rounded (nonzeroProfile (0 : AES.Word) f) hp
  have hscale : (2 : ℝ) ^ (64 : ℕ) / 2 = (2 : ℝ) ^ (63 : ℕ) := by norm_num
  rw [hscale] at h
  exact h.trans (mul_le_mul_of_nonneg_left he (by positivity))

end AES8.PaperRoundedOutput
