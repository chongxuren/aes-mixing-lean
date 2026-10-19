import AESPaper.CenteredConvolution
import AESMixing.SubstitutionDegree

/-!
# Balanced four-source convolution smoothing

All four inputs are probability laws. Marked inputs have a common centered
energy cap; unmarked inputs need no further analytic hypothesis. If at least
two positions are marked, either both lie in one balanced pair, or each pair
contains one. Probability convolution contracts centered energy, so both
cases retain the two-source product bound. Inactive point masses are covered
by the general probability-law interface without a special-case expansion.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.FourSourceConvolution
open AESMixing AESPaper.CenteredConvolution

variable {V : Type*} [Fintype V] [AddCommGroup V]

/-- The two balanced pairs preserve the actual four independent source laws. -/
def fourfold (f : Fin 4 → V → ℝ) : V → ℝ :=
  convolution (convolution (f 0) (f 1)) (convolution (f 2) (f 3))

theorem fourfold_mass (f : Fin 4 → V → ℝ)
    (hm : ∀ i, ∑ x, f i x = 1) : (∑ x, fourfold f x) = 1 := by
  exact convolution_unit_mass _ _
    (convolution_unit_mass _ _ (hm 0) (hm 1))
    (convolution_unit_mass _ _ (hm 2) (hm 3))

theorem fourfold_nonnegative (f : Fin 4 → V → ℝ)
    (hn : ∀ i x, 0 ≤ f i x) (x : V) : 0 ≤ fourfold f x := by
  exact convolution_nonnegative _ _
    (convolution_nonnegative _ _ (hn 0) (hn 1))
    (convolution_nonnegative _ _ (hn 2) (hn 3)) x

/-- Two capped unit-mass laws supply the one-cardinality product estimate. -/
theorem two_law_centeredEnergy_le (p q : V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (hep : centeredEnergy p ≤ a) (heq : centeredEnergy q ≤ a) :
    centeredEnergy (convolution p q) ≤ (Fintype.card V : ℝ) * a ^ 2 := by
  have hmul : centeredEnergy p * centeredEnergy q ≤ a * a :=
    mul_le_mul hep heq (centeredEnergy_nonnegative q) ha
  calc
    _ ≤ (Fintype.card V : ℝ) * centeredEnergy p * centeredEnergy q :=
      centeredEnergy_convolution_le p q hp hq
    _ = (Fintype.card V : ℝ) * (centeredEnergy p * centeredEnergy q) := by ring
    _ ≤ (Fintype.card V : ℝ) * (a * a) :=
      mul_le_mul_of_nonneg_left hmul (le_of_lt real_card_pos)
    _ = _ := by ring

/-- A finite logical classification; no field or probability calculation is
hidden in the sixteen-pattern check. -/
theorem two_marked_pair_cases : ∀ b : Fin 4 → Bool, 2 ≤ residualDegree b →
    (b 0 = true ∧ b 1 = true) ∨ (b 2 = true ∧ b 3 = true) ∨
      ((b 0 = true ∨ b 1 = true) ∧ (b 2 = true ∨ b 3 = true)) := by decide

/-- At least two capped positions suffice; the other laws need only be
nonnegative and have unit mass. Dependence is not asserted for the output. -/
theorem fourfold_centeredEnergy_le (f : Fin 4 → V → ℝ)
    (b : Fin 4 → Bool) (a : ℝ) (ha : 0 ≤ a)
    (hn : ∀ i x, 0 ≤ f i x) (hm : ∀ i, ∑ x, f i x = 1)
    (he : ∀ i, b i = true → centeredEnergy (f i) ≤ a)
    (hb : 2 ≤ residualDegree b) :
    centeredEnergy (fourfold f) ≤ (Fintype.card V : ℝ) * a ^ 2 := by
  let p := convolution (f 0) (f 1)
  let q := convolution (f 2) (f 3)
  have hpn : ∀ x, 0 ≤ p x := convolution_nonnegative _ _ (hn 0) (hn 1)
  have hqn : ∀ x, 0 ≤ q x := convolution_nonnegative _ _ (hn 2) (hn 3)
  have hpm : (∑ x, p x) = 1 := convolution_unit_mass _ _ (hm 0) (hm 1)
  have hqm : (∑ x, q x) = 1 := convolution_unit_mass _ _ (hm 2) (hm 3)
  have hpe (h : b 0 = true ∨ b 1 = true) : centeredEnergy p ≤ a := by
    rcases h with h0 | h1
    · exact (centeredEnergy_convolution_le_left _ _ (hn 1) (hm 1)).trans (he 0 h0)
    · exact (centeredEnergy_convolution_le_right _ _ (hn 0) (hm 0)).trans (he 1 h1)
  have hqe (h : b 2 = true ∨ b 3 = true) : centeredEnergy q ≤ a := by
    rcases h with h2 | h3
    · exact (centeredEnergy_convolution_le_left _ _ (hn 3) (hm 3)).trans (he 2 h2)
    · exact (centeredEnergy_convolution_le_right _ _ (hn 2) (hm 2)).trans (he 3 h3)
  change centeredEnergy (convolution p q) ≤ _
  rcases two_marked_pair_cases b hb with h01 | h23 | hcross
  · exact (centeredEnergy_convolution_le_left p q hqn hqm).trans
      (two_law_centeredEnergy_le _ _ a ha (hm 0) (hm 1) (he 0 h01.1) (he 1 h01.2))
  · exact (centeredEnergy_convolution_le_right p q hpn hpm).trans
      (two_law_centeredEnergy_le _ _ a ha (hm 2) (hm 3) (he 2 h23.1) (he 3 h23.2))
  · exact two_law_centeredEnergy_le p q a ha hpm hqm (hpe hcross.1) (hqe hcross.2)

/-- The marginal budget needed for two, three, or four active source words. -/
theorem fourfold_fifth_bound (f : Fin 4 → V → ℝ) (b : Fin 4 → Bool)
    (hn : ∀ i x, 0 ≤ f i x) (hm : ∀ i, ∑ x, f i x = 1)
    (he : ∀ i, b i = true →
      centeredEnergy (f i) ≤ 1 / (5 * (Fintype.card V : ℝ)))
    (hb : 2 ≤ residualDegree b) :
    centeredEnergy (fourfold f) ≤ 1 / (25 * (Fintype.card V : ℝ)) := by
  have ha : 0 ≤ 1 / (5 * (Fintype.card V : ℝ)) :=
    div_nonneg (by norm_num) (mul_nonneg (by norm_num) (le_of_lt real_card_pos))
  calc
    _ ≤ (Fintype.card V : ℝ) * (1 / (5 * (Fintype.card V : ℝ))) ^ 2 :=
      fourfold_centeredEnergy_le f b _ ha hn hm he hb
    _ = _ := by
      field_simp [real_card_ne_zero] <;> ring

end AESPaper.FourSourceConvolution
