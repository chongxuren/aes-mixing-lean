import AESConcrete.TripleResponse

/-!
# Three exclusion weights with surviving pair intersections

Only the triple intersection is assumed to kill the kernel. All three line
responses remain in the signed inclusion-exclusion identity. The amplitude
is arbitrary and shared by all seven terms. Norm aggregation precedes squaring.

Candidate for the constructive AES (12,6) route; no accepted cap is asserted.
Independent retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target remain unchanged. No attacks.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.SevenResponse
open AESMixing
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WeightedResponse (rawResponse zeroResponse weightedResponse normalizer)
open AESConcrete.TripleResponse (intersectionResponse)

section Identity
variable {S Y V : Type*} [Fintype S] [AddCommGroup V] [Fintype V] [DecidableEq V]

omit [Fintype S] in
private theorem weighted_summand (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V)
    (hzero : ∀ y x, c₀ x = 0 → c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (y : Y) (x : S) :
    h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) *
        nonzeroUniform (c₂ x) * K y x =
      (h x * K y x - (if c₀ x = 0 then h x * K y x else 0) -
        (if c₁ x = 0 then h x * K y x else 0) -
        (if c₂ x = 0 then h x * K y x else 0) +
        (if c₀ x = 0 ∧ c₁ x = 0 then h x * K y x else 0) +
        (if c₀ x = 0 ∧ c₂ x = 0 then h x * K y x else 0) +
        (if c₁ x = 0 ∧ c₂ x = 0 then h x * K y x else 0)) / normalizer V := by
  by_cases h₀ : c₀ x = 0 <;> by_cases h₁ : c₁ x = 0 <;> by_cases h₂ : c₂ x = 0
  · rw [hzero y x h₀ h₁ h₂]
    simp
  all_goals
    simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁, h₂,
      normalizer, div_eq_mul_inv]
    <;> ring

/-- Full minus three planes plus three lines, on the same finite source. -/
theorem weightedResponse_eq_seven (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V)
    (hzero : ∀ y x, c₀ x = 0 → c₁ x = 0 → c₂ x = 0 → K y x = 0) :
    weightedResponse h K c₀ c₁ c₂ = fun y =>
      (rawResponse h K y - zeroResponse h K c₀ y - zeroResponse h K c₁ y -
        zeroResponse h K c₂ y + intersectionResponse h K c₀ c₁ y +
        intersectionResponse h K c₀ c₂ y + intersectionResponse h K c₁ c₂ y) /
          normalizer V := by
  funext y
  unfold weightedResponse
  simp_rw [weighted_summand h K c₀ c₁ c₂ hzero y]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    rawResponse, zeroResponse, intersectionResponse]

end Identity

section Energy
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem seven_response_l2 (A B C D E F G : Y → ℝ) (d : ℝ) :
    l2 (fun y => (A y - B y - C y - D y + E y + F y + G y) / d) ≤
      (l2 A + l2 B + l2 C + l2 D + l2 E + l2 F + l2 G) / |d| := by
  rw [WeightedResponse.l2_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg d)
  have hab := WeightedResponse.l2_sub_le A B
  have habc := (WeightedResponse.l2_sub_le (fun y => A y - B y) C).trans
    (add_le_add hab (le_refl (l2 C)))
  have habcd := (WeightedResponse.l2_sub_le (fun y => A y - B y - C y) D).trans
    (add_le_add habc (le_refl (l2 D)))
  have he := (l2_add_le (fun y => A y - B y - C y - D y) E).trans
    (add_le_add habcd (le_refl (l2 E)))
  have hf := (l2_add_le (fun y => A y - B y - C y - D y + E y) F).trans
    (add_le_add he (le_refl (l2 F)))
  exact (l2_add_le (fun y => A y - B y - C y - D y + E y + F y) G).trans
    (add_le_add hf (le_refl (l2 G)))

/-- Three equal plane caps and three equal line caps, all charged to one input. -/
theorem seven_response_l2_le (A B C D E F G : Y → ℝ) (g : Z → ℝ)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : (∑ y, A y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, B y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, C y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, D y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hE : (∑ y, E y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hF : (∑ y, F y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hG : (∑ y, G y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2) :
    l2 (fun y => (A y - B y - C y - D y + E y + F y + G y) / d) ≤
      ((a + 3 * b + 3 * c) / |d|) * l2 g := by
  calc
    _ ≤ (l2 A + l2 B + l2 C + l2 D + l2 E + l2 F + l2 G) / |d| :=
      seven_response_l2 A B C D E F G d
    _ ≤ (a * l2 g + b * l2 g + b * l2 g + b * l2 g +
        c * l2 g + c * l2 g + c * l2 g) / |d| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg d)
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (l2_le_of_energy A g a ha hA) (l2_le_of_energy B g b hb hB))
        (l2_le_of_energy C g b hb hC)) (l2_le_of_energy D g b hb hD))
        (l2_le_of_energy E g c hc hE)) (l2_le_of_energy F g c hc hF))
        (l2_le_of_energy G g c hc hG)
    _ = _ := by ring

theorem weightedResponse_energy_le
    (hn : 1 ≤ Fintype.card V) (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (hzero : ∀ y x, c₀ x = 0 → c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hE : (∑ y, intersectionResponse h K c₀ c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hF : (∑ y, intersectionResponse h K c₀ c₂ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hG : (∑ y, intersectionResponse h K c₁ c₂ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ c₂ y ^ 2) ≤
      ((a + 3 * b + 3 * c) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 3) *
        ∑ z, g z ^ 2 := by
  have hl := seven_response_l2_le (rawResponse h K) (zeroResponse h K c₀)
    (zeroResponse h K c₁) (zeroResponse h K c₂)
    (intersectionResponse h K c₀ c₁) (intersectionResponse h K c₀ c₂)
    (intersectionResponse h K c₁ c₂) g a b c (normalizer V) ha hb hc
    hA hB hC hD hE hF hG
  rw [← weightedResponse_eq_seven h K c₀ c₁ c₂ hzero] at hl
  rw [abs_of_nonneg (WeightedResponse.normalizer_nonneg V)] at hl
  have hcoef : 0 ≤ (a + 3 * b + 3 * c) / normalizer V :=
    div_nonneg (by positivity) (WeightedResponse.normalizer_nonneg V)
  have hs := (sq_le_sq₀ (l2_nonneg (weightedResponse h K c₀ c₁ c₂))
    (mul_nonneg hcoef (l2_nonneg g))).mpr hl
  simpa only [mul_pow, l2_sq, div_pow, WeightedResponse.normalizer_sq V hn] using hs

end Energy
end AESConcrete.SevenResponse
