import AESConcrete.NonzeroUniformGraphCap
import AESMixing.L2Sums

/-!
# Three exclusion weights and their four surviving signed responses

This generic finite-source identity precedes every norm bound. Each of the
three pairwise zero intersections must annihilate the residual kernel. The
amplitude is arbitrary and signed; in particular no value at zero is removed.
All sums and `l2` norms use counting measure. Geometry, source normalization,
and the four separate response estimates are explicit external obligations.

Constructive mathematics only; no attacks. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct pairs and the fixed
10/14/16 target remain unchanged. This source alone asserts no AES cap,
inventory admission, compilation, or independent review.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WeightedResponse
open AESMixing
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)

section Responses
variable {S Y V : Type*} [Fintype S]

/-- The response on the full source, with no uniform normalization. -/
def rawResponse (h : S → ℝ) (K : Y → S → ℝ) (y : Y) : ℝ :=
  ∑ x, h x * K y x

/-- One zero constraint, counted on its original finite source. -/
def zeroResponse [Zero V] [DecidableEq V]
    (h : S → ℝ) (K : Y → S → ℝ) (c : S → V) (y : Y) : ℝ :=
  ∑ x, if c x = 0 then h x * K y x else 0

/-- The common denominator of exactly three nonzero-uniform legs. -/
def normalizer (V : Type*) [Fintype V] : ℝ :=
  (Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 3

theorem normalizer_nonneg (V : Type*) [Fintype V] : 0 ≤ normalizer V := by
  unfold normalizer
  positivity

theorem normalizer_pos (V : Type*) [Fintype V]
    (hn : 1 < Fintype.card V) : 0 < normalizer V := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold normalizer
  exact pow_pos (Real.sqrt_pos.2 (by linarith)) 3

theorem normalizer_sq (V : Type*) [Fintype V]
    (hn : 1 ≤ Fintype.card V) :
    normalizer V ^ 2 = ((Fintype.card V : ℝ) - 1) ^ 3 := by
  have hn' : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hq : 0 ≤ (Fintype.card V : ℝ) - 1 := by linarith
  unfold normalizer
  calc
    ((Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 3) ^ 2 =
        ((Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 2) ^ 3 := by ring
    _ = _ := by rw [Real.sq_sqrt hq]

variable [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The actual three normalized exclusion weights; none is charged twice. -/
def weightedResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (y : Y) : ℝ :=
  ∑ x, h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) *
    nonzeroUniform (c₂ x) * K y x

-- Editorial decision: use kernel vanishing, rather than amplitude vanishing,
-- so the same unrestricted signed h (including h(0)) remains in every term.
omit [Fintype S] in
private theorem weighted_summand (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (y : Y) (x : S) :
    h x * nonzeroUniform (c₀ x) * nonzeroUniform (c₁ x) *
        nonzeroUniform (c₂ x) * K y x =
      (h x * K y x - (if c₀ x = 0 then h x * K y x else 0) -
        (if c₁ x = 0 then h x * K y x else 0) -
        (if c₂ x = 0 then h x * K y x else 0)) / normalizer V := by
  by_cases h₀ : c₀ x = 0
  · by_cases h₁ : c₁ x = 0
    · rw [h₀₁ y x h₀ h₁]
      simp
    · by_cases h₂ : c₂ x = 0
      · rw [h₀₂ y x h₀ h₂]
        simp
      · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁, h₂]
  · by_cases h₁ : c₁ x = 0
    · by_cases h₂ : c₂ x = 0
      · rw [h₁₂ y x h₁ h₂]
        simp
      · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁, h₂]
    · by_cases h₂ : c₂ x = 0
      · simp [nonzeroUniform, supportConstant, identityKernel, h₀, h₁, h₂]
      · simp only [nonzeroUniform, supportConstant, Bool.false_eq_true, if_false,
          identityKernel, if_neg h₀, if_neg h₁, if_neg h₂, sub_zero,
          normalizer, div_eq_mul_inv, one_mul]
        ring

/-- Exact signed inclusion-exclusion. Pair and triple terms vanish before
any norm is taken. No positivity, independence, or `h(0)=0` premise is used. -/
theorem weightedResponse_eq_four (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0) :
    weightedResponse h K c₀ c₁ c₂ = fun y =>
      (rawResponse h K y - zeroResponse h K c₀ y -
        zeroResponse h K c₁ y - zeroResponse h K c₂ y) / normalizer V := by
  funext y
  unfold weightedResponse
  simp_rw [weighted_summand h K c₀ c₁ c₂ h₀₁ h₀₂ h₁₂ y]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, rawResponse, zeroResponse]

end Responses

section CountingNorm
variable {Y Z : Type*} [Fintype Y] [Fintype Z]

/-- A signed subtraction satisfies the counting-measure triangle inequality. -/
theorem l2_sub_le (A B : Y → ℝ) :
    l2 (fun y => A y - B y) ≤ l2 A + l2 B := by
  have he : (fun y => A y - B y) = A + (fun y => (-1 : ℝ) * B y) := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact (l2_add_le A (fun y => (-1 : ℝ) * B y)).trans_eq (by
    rw [l2_scale]
    norm_num)

theorem l2_div (A : Y → ℝ) (d : ℝ) :
    l2 (fun y => A y / d) = l2 A / |d| := by
  have he : (fun y => A y / d) = fun y => (1 / d) * A y := by
    funext y
    ring
  rw [he, l2_scale, abs_div, abs_one]
  ring

/-- Four signed responses are combined only by the triangle inequality.
There is no output orthogonality premise. -/
theorem four_response_l2 (A B C D : Y → ℝ) (d : ℝ) :
    l2 (fun y => (A y - B y - C y - D y) / d) ≤
      (l2 A + l2 B + l2 C + l2 D) / |d| := by
  rw [l2_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg d)
  exact (l2_sub_le (fun y => A y - B y - C y) D).trans
    (add_le_add ((l2_sub_le (fun y => A y - B y) C).trans
      (add_le_add (l2_sub_le A B) (le_refl (l2 C)))) (le_refl (l2 D)))

/-- Each term retains its own nonnegative energy cap against one common
counting input norm. The common input need not have the source's type. -/
theorem four_response_l2_le (A B C D : Y → ℝ) (g : Z → ℝ)
    (a b c e d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, A y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, B y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, C y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, D y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    l2 (fun y => (A y - B y - C y - D y) / d) ≤
      ((a + b + c + e) / |d|) * l2 g := by
  calc
    _ ≤ (l2 A + l2 B + l2 C + l2 D) / |d| := four_response_l2 A B C D d
    _ ≤ (a * l2 g + b * l2 g + c * l2 g + e * l2 g) / |d| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg d)
      exact add_le_add (add_le_add (add_le_add
        (l2_le_of_energy A g a ha hA) (l2_le_of_energy B g b hb hB))
        (l2_le_of_energy C g c hc hC)) (l2_le_of_energy D g e he hD)
    _ = _ := by ring

end CountingNorm

section WeightedBounds
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The four-term identity and heterogeneous counting-energy bounds combine
without changing the signed amplitude or introducing a source-fiber count. -/
theorem weightedResponse_l2_le (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    l2 (weightedResponse h K c₀ c₁ c₂) ≤
      ((a + b + c + e) / normalizer V) * l2 g := by
  rw [weightedResponse_eq_four h K c₀ c₁ c₂ h₀₁ h₀₂ h₁₂]
  simpa only [abs_of_nonneg (normalizer_nonneg V)] using
    four_response_l2_le (rawResponse h K) (zeroResponse h K c₀)
      (zeroResponse h K c₁) (zeroResponse h K c₂) g
      a b c e (normalizer V) ha hb hc he hA hB hC hD

/-- Squaring occurs once, after all four signed norms have been added. -/
theorem weightedResponse_energy_le (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ c₂ y ^ 2) ≤
      ((a + b + c + e) / normalizer V) ^ 2 * ∑ z, g z ^ 2 := by
  have hcoef : 0 ≤ (a + b + c + e) / normalizer V :=
    div_nonneg (by linarith) (normalizer_nonneg V)
  have hs := (sq_le_sq₀ (l2_nonneg (weightedResponse h K c₀ c₁ c₂))
    (mul_nonneg hcoef (l2_nonneg g))).mpr
      (weightedResponse_l2_le h K c₀ c₁ c₂ g h₀₁ h₀₂ h₁₂
        a b c e ha hb hc he hA hB hC hD)
  simpa only [mul_pow, l2_sq] using hs

/-- The denominator in energy is exactly `(card V - 1)^3`. -/
theorem weightedResponse_energy_le_normalized
    (hn : 1 ≤ Fintype.card V) (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ e ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ c₂ y ^ 2) ≤
      ((a + b + c + e) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 3) *
        ∑ z, g z ^ 2 := by
  simpa only [div_pow, normalizer_sq V hn] using
    weightedResponse_energy_le h K c₀ c₁ c₂ g h₀₁ h₀₂ h₁₂
      a b c e ha hb hc he hA hB hC hD

/-- A plane cap with factor `s` and three identical line caps give exactly
the common `(s+3)^2` factor, without rounding or output orthogonality. -/
theorem weightedResponse_common_energy_le
    (hn : 1 ≤ Fintype.card V) (h : S → ℝ) (K : Y → S → ℝ)
    (c₀ c₁ c₂ : S → V) (g : Z → ℝ)
    (h₀₁ : ∀ y x, c₀ x = 0 → c₁ x = 0 → K y x = 0)
    (h₀₂ : ∀ y x, c₀ x = 0 → c₂ x = 0 → K y x = 0)
    (h₁₂ : ∀ y x, c₁ x = 0 → c₂ x = 0 → K y x = 0)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hA : (∑ y, rawResponse h K y ^ 2) ≤ (s * a) ^ 2 * ∑ z, g z ^ 2)
    (hB : (∑ y, zeroResponse h K c₀ y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hC : (∑ y, zeroResponse h K c₁ y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hD : (∑ y, zeroResponse h K c₂ y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K c₀ c₁ c₂ y ^ 2) ≤
      (a ^ 2 * (s + 3) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 3) *
        ∑ z, g z ^ 2 := by
  exact (weightedResponse_energy_le_normalized hn h K c₀ c₁ c₂ g h₀₁ h₀₂ h₁₂
    (s * a) a a a (mul_nonneg hs ha) ha ha ha hA hB hC hD).trans_eq (by ring)

end WeightedBounds
end AESConcrete.WeightedResponse
