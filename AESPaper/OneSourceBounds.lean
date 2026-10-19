import AESPaper.OneSourceEnergies
import AESPaper.FourSourcePattern

/-!
# The positive residual-degree bounds for one active source word

Each degree is a sum of orthogonal actual position patterns. Degree one
uses the second-response bound and three uniform activity factors. Degrees
two through four use the capped common-source second Gram moment, retaining
exact binomial multiplicities. The full-state uniform reference is removed
using its proved degree-zero identity. No independent-output assumption.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.OneSourceBounds
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)

/-- Orthogonality supplies the number of position patterns, rather than a
triangle-inequality factor. The probability law may be correlated. -/
theorem degree_energy_of_pattern_le (j : Fin 5) (f : AES.WordState → ℝ) (C : ℝ)
    (h : ∀ b : Fin 4 → Bool, degreeIndex b = j →
      (∑ y, action (productProjection (0 : AES.Word) b) f y ^ 2) ≤ C) :
    (∑ y, degreeComponent (0 : AES.Word) j f y ^ 2) ≤ (Nat.choose 4 j.val : ℝ)*C := by
  rw [degreeComponent_energy (0 : AES.Word) ProfileSpace.word_card_gt_one,
    ← FourSourcePattern.degree_constant_sum j C]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : degreeIndex b = j
  · simp only [hb, if_true]
    exact h b hb
  · simp only [hb, if_false, le_refl]

theorem degree_one_energy_le (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) 1 (OneSourceLaw.law k a) y ^ 2) ≤
      4 * ((49/(5*q^2)) * (1/(q-1))^3) := by
  have h := degree_energy_of_pattern_le 1 (OneSourceLaw.law k a)
    ((49/(5*q^2)) * (1/(q-1))^3)
    (fun b hb => OneSourceEnergies.pattern_one_energy_le b hb k a ha)
  norm_num [Nat.choose] at h
  simpa only [one_div, inv_pow] using h

theorem pattern_high_energy_le (b : Fin 4 → Bool) (hb : 2 ≤ residualDegree b)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, action (productProjection (0 : AES.Word) b) (OneSourceLaw.law k a) y ^ 2) ≤
      (20/q)^2 * (300/q)^2 * (2/(15*q))^(residualDegree b-2) *
        (1/(q-1))^(4-residualDegree b) := by
  rw [OneSourceEnergies.pattern_energy b k a ha]
  exact FourSourcePattern.mixed_bound (OneSourceEnergies.G k) (wordLaw a)
    (20/q) (300/q) (2/(15*q)) (1/(q-1))
    (by norm_num [q]) (by norm_num [q]) (by norm_num [q])
    (fun x => (StartingWord.wordLaw_abs_point_lt a x ha).le)
    (OneSourceEnergies.G_entry k) (OneSourceEnergies.G_moment k) b hb

theorem degree_high_energy_le (j : Fin 5) (hj : 2 ≤ j.val)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) j (OneSourceLaw.law k a) y ^ 2) ≤
      (Nat.choose 4 j.val : ℝ) * ((20/q)^2 * (300/q)^2 * (2/(15*q))^(j.val-2) *
        (1/(q-1))^(4-j.val)) := by
  apply degree_energy_of_pattern_le
  intro b hb
  have hd : residualDegree b = j.val := congrArg Fin.val hb
  simpa only [hd] using pattern_high_energy_le b (by omega) k a ha

/-- Exact rational arithmetic turns all four proved energy bounds into the
paper's initial positive-degree entries. -/
theorem scaled_positive_energy_lt (j : Fin 5) (hj : j ≠ 0)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    q^5 * (∑ y, degreeComponent (0 : AES.Word) j
      (OneSourceLaw.law k a-uniformExcept (0 : AES.WordState)) y ^ 2) <
        AESPaper.initialProfile j ^ 2 := by
  rw [OneSourceEnergies.centered_positive_degree j hj k a]
  have hq : 0 ≤ q^5 := by norm_num [q]
  fin_cases j
  · exact (hj rfl).elim
  · exact (mul_le_mul_of_nonneg_left (degree_one_energy_le k a ha) hq).trans_lt
      (by norm_num [q, AESPaper.initialProfile, Nat.choose])
  · exact (mul_le_mul_of_nonneg_left (degree_high_energy_le 2 (by decide) k a ha) hq).trans_lt
      (by norm_num [q, AESPaper.initialProfile, Nat.choose])
  · exact (mul_le_mul_of_nonneg_left (degree_high_energy_le 3 (by decide) k a ha) hq).trans_lt
      (by norm_num [q, AESPaper.initialProfile, Nat.choose])
  · exact (mul_le_mul_of_nonneg_left (degree_high_energy_le 4 (by decide) k a ha) hq).trans_lt
      (by norm_num [q, AESPaper.initialProfile, Nat.choose])

end AESPaper.OneSourceBounds
