import AESConcrete.SevenResponse

/-!
# Three exclusion weights with both endpoint responses retained

The support indices are `(12,10)`. The arbitrary signed amplitude is shared by
all eight terms. No endpoint cancellation or orthogonality of signed responses
is assumed. Physical event identification, energy bounds and support
aggregation remain caller obligations.

Fixed independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference law and AES10/14/16 scope.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.EightResponse
open AESMixing
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WeightedResponse (rawResponse zeroResponse weightedResponse normalizer)
open AESConcrete.TripleResponse (intersectionResponse)

section Identity
variable {S Y V : Type*} [Fintype S] [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The simultaneous three-event response is retained, including its sign. -/
def tripleIntersectionResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (y : Y) : ℝ :=
  ∑ x, if c₀ x = 0 ∧ c₁ x = 0 ∧ c₂ x = 0 then h x * K y x else 0

omit [Fintype S] in
private theorem weighted_summand (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (y : Y) (x : S) :
    h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) *
        nonzeroUniform (c₂ x) * K y x =
      (h x * K y x - (if c₀ x = 0 then h x * K y x else 0) -
        (if c₁ x = 0 then h x * K y x else 0) -
        (if c₂ x = 0 then h x * K y x else 0) +
        (if c₀ x = 0 ∧ c₁ x = 0 then h x * K y x else 0) +
        (if c₀ x = 0 ∧ c₂ x = 0 then h x * K y x else 0) +
        (if c₁ x = 0 ∧ c₂ x = 0 then h x * K y x else 0) -
        (if c₀ x = 0 ∧ c₁ x = 0 ∧ c₂ x = 0 then h x * K y x else 0)) /
          normalizer V := by
  by_cases h₀ : c₀ x = 0 <;> by_cases h₁ : c₁ x = 0 <;> by_cases h₂ : c₂ x = 0
  all_goals
    simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁, h₂,
      normalizer, div_eq_mul_inv] <;> ring_nf

/-- Complete inclusion-exclusion on the original finite source. -/
theorem weightedResponse_eq_eight (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) :
    weightedResponse h K c₀ c₁ c₂ = fun y =>
      (rawResponse h K y - zeroResponse h K c₀ y - zeroResponse h K c₁ y -
        zeroResponse h K c₂ y + intersectionResponse h K c₀ c₁ y +
        intersectionResponse h K c₀ c₂ y + intersectionResponse h K c₁ c₂ y -
        tripleIntersectionResponse h K c₀ c₁ c₂ y) / normalizer V := by
  funext y
  unfold weightedResponse
  simp_rw [weighted_summand h K c₀ c₁ c₂ y]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    rawResponse, zeroResponse, intersectionResponse, tripleIntersectionResponse]

end Identity

section Energy
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Triangle inequality with the surviving triple intersection. -/
theorem eight_response_l2 (A B C D E F G H : Y → ℝ) (t : ℝ) :
    l2 (fun y => (A y - B y - C y - D y + E y + F y + G y - H y) / t) ≤
      (l2 A + l2 B + l2 C + l2 D + l2 E + l2 F + l2 G + l2 H) / |t| := by
  rw [WeightedResponse.l2_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg t)
  have hseven : l2 (fun y => A y - B y - C y - D y + E y + F y + G y) ≤
      l2 A + l2 B + l2 C + l2 D + l2 E + l2 F + l2 G := by
    simpa only [div_one, abs_one] using
      (SevenResponse.seven_response_l2 A B C D E F G 1)
  exact (WeightedResponse.l2_sub_le
    (fun y => A y - B y - C y - D y + E y + F y + G y) H).trans
      (add_le_add hseven (le_refl (l2 H)))

/-- All responses are charged to the same signed input amplitude. -/
theorem eight_response_l2_le (A B C D E F G H : Y → ℝ) (g : Z → ℝ)
    (a b c d t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : (∑ y, A y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, B y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, C y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, D y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hE : (∑ y, E y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hF : (∑ y, F y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hG : (∑ y, G y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hH : (∑ y, H y ^ 2) ≤ d ^ 2 * ∑ z, g z ^ 2) :
    l2 (fun y => (A y - B y - C y - D y + E y + F y + G y - H y) / t) ≤
      ((a + 3 * b + 3 * c + d) / |t|) * l2 g := by
  calc
    _ ≤ (l2 A + l2 B + l2 C + l2 D + l2 E + l2 F + l2 G + l2 H) / |t| :=
      eight_response_l2 A B C D E F G H t
    _ ≤ (a * l2 g + b * l2 g + b * l2 g + b * l2 g +
        c * l2 g + c * l2 g + c * l2 g + d * l2 g) / |t| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg t)
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add (l2_le_of_energy A g a ha hA) (l2_le_of_energy B g b hb hB))
        (l2_le_of_energy C g b hb hC)) (l2_le_of_energy D g b hb hD))
        (l2_le_of_energy E g c hc hE)) (l2_le_of_energy F g c hc hF))
        (l2_le_of_energy G g c hc hG)) (l2_le_of_energy H g d hd hH)
    _ = _ := by ring

/-- Three equal single-event caps and three equal double-event caps; both
endpoint caps are explicit. This theorem supplies no physical AES premises. -/
theorem weightedResponse_energy_le
    (hn : 1 ≤ Fintype.card V) (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hE : (∑ y, intersectionResponse h K c₀ c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hF : (∑ y, intersectionResponse h K c₀ c₂ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hG : (∑ y, intersectionResponse h K c₁ c₂ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hH : (∑ y, tripleIntersectionResponse h K c₀ c₁ c₂ y ^ 2) ≤
      d ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ c₂ y ^ 2) ≤
      ((a + 3 * b + 3 * c + d) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 3) *
        ∑ z, g z ^ 2 := by
  have hl := eight_response_l2_le (rawResponse h K) (zeroResponse h K c₀)
    (zeroResponse h K c₁) (zeroResponse h K c₂)
    (intersectionResponse h K c₀ c₁) (intersectionResponse h K c₀ c₂)
    (intersectionResponse h K c₁ c₂) (tripleIntersectionResponse h K c₀ c₁ c₂)
    g a b c d (normalizer V) ha hb hc hd hA hB hC hD hE hF hG hH
  rw [← weightedResponse_eq_eight h K c₀ c₁ c₂] at hl
  rw [abs_of_nonneg (WeightedResponse.normalizer_nonneg V)] at hl
  have hcoef : 0 ≤ (a + 3 * b + 3 * c + d) / normalizer V :=
    div_nonneg (by positivity) (WeightedResponse.normalizer_nonneg V)
  have hs := (sq_le_sq₀ (l2_nonneg (weightedResponse h K c₀ c₁ c₂))
    (mul_nonneg hcoef (l2_nonneg g))).mpr hl
  simpa only [mul_pow, l2_sq, div_pow, WeightedResponse.normalizer_sq V hn] using hs

end Energy
end AESConcrete.EightResponse
