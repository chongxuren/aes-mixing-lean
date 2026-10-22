import AESConcrete.WeightedResponse

/-!
# Two exclusion weights with a surviving intersection response

The exact signed identity is full minus two planes plus their intersection.
The intersection is retained: it is generally a nonzero line for the `(12,9)`
source. All four responses preserve the same arbitrary signed amplitude.
Counting-measure triangle aggregation precedes squaring. This generic lemma
does not assert an AES cap before the actual geometry and energy hypotheses
are supplied. Constructive mathematics only; no attacks.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleResponse
open AESMixing
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WeightedResponse (rawResponse zeroResponse)

section Identity
variable {S Y V : Type*} [Fintype S] [AddCommGroup V] [Fintype V] [DecidableEq V]

def normalizer (V : Type*) [Fintype V] : ℝ :=
  (Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 2

theorem normalizer_nonneg (V : Type*) [Fintype V] : 0 ≤ normalizer V :=
  sq_nonneg _

theorem normalizer_eq (V : Type*) [Fintype V] (hn : 1 ≤ Fintype.card V) :
    normalizer V = (Fintype.card V : ℝ) - 1 := by
  have hn' : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  exact Real.sq_sqrt (by linarith)

/-- The intersection is counted on the same original finite source. -/
def intersectionResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ : S → V) (y : Y) : ℝ :=
  ∑ x, if c₀ x = 0 ∧ c₁ x = 0 then h x * K y x else 0

def weightedResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ : S → V) (y : Y) : ℝ :=
  ∑ x, h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) * K y x

omit [Fintype S] in
private theorem weighted_summand (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ : S → V) (y : Y) (x : S) :
    h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) * K y x =
      (h x * K y x - (if c₀ x = 0 then h x * K y x else 0) -
        (if c₁ x = 0 then h x * K y x else 0) +
        (if c₀ x = 0 ∧ c₁ x = 0 then h x * K y x else 0)) / normalizer V := by
  by_cases h₀ : c₀ x = 0
  · by_cases h₁ : c₁ x = 0
    · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁]
    · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁]
  · by_cases h₁ : c₁ x = 0
    · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁]
    · have h₀₁ : ¬ (c₀ x = 0 ∧ c₁ x = 0) := fun hz => h₀ hz.1
      simp only [nonzeroUniform, supportConstant, Bool.false_eq_true, if_false,
        identityKernel, if_neg h₀, if_neg h₁, if_neg h₀₁, sub_zero, add_zero,
        normalizer, div_eq_mul_inv, one_mul]
      ring

/-- No cancellation or orthogonality is assumed for the intersection. -/
theorem weightedResponse_eq_four (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ : S → V) :
    weightedResponse h K c₀ c₁ = fun y =>
      (rawResponse h K y - zeroResponse h K c₀ y - zeroResponse h K c₁ y +
        intersectionResponse h K c₀ c₁ y) / normalizer V := by
  funext y
  unfold weightedResponse
  simp_rw [weighted_summand h K c₀ c₁ y]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    rawResponse, zeroResponse, intersectionResponse]

end Identity

section Energy
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem four_response_l2_le (A B C D : Y → ℝ) (g : Z → ℝ)
    (a b c e d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, A y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, B y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, C y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, D y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    l2 (fun y => (A y - B y - C y + D y) / d) ≤
      ((a + b + c + e) / |d|) * l2 g := by
  have hD' : (∑ y, (-D y) ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2 := by
    simpa only [neg_sq] using hD
  simpa only [sub_neg_eq_add] using
    WeightedResponse.four_response_l2_le A B C (fun y => -D y) g
      a b c e d ha hb hc he hA hB hC hD'

/-- Each of the four energy estimates is against one common original input. -/
theorem weightedResponse_energy_le
    (hn : 1 ≤ Fintype.card V) (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ : S → V) (g : Z → ℝ)
    (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, intersectionResponse h K c₀ c₁ y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ y ^ 2) ≤
      ((a + b + c + e) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 2) *
        ∑ z, g z ^ 2 := by
  have hl := four_response_l2_le (rawResponse h K) (zeroResponse h K c₀)
    (zeroResponse h K c₁) (intersectionResponse h K c₀ c₁) g
    a b c e (normalizer V) ha hb hc he hA hB hC hD
  rw [← weightedResponse_eq_four] at hl
  rw [abs_of_nonneg (normalizer_nonneg V)] at hl
  have hcoef : 0 ≤ (a + b + c + e) / normalizer V :=
    div_nonneg (by linarith) (normalizer_nonneg V)
  have hs := (sq_le_sq₀ (l2_nonneg (weightedResponse h K c₀ c₁))
    (mul_nonneg hcoef (l2_nonneg g))).mpr hl
  simpa only [mul_pow, l2_sq, div_pow, normalizer_eq V hn] using hs

end Energy
end AESConcrete.TripleResponse
