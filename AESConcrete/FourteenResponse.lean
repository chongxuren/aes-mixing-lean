import AESConcrete.TripleResponse

/-!
# Future four-exclusion response with fourteen surviving intersections

Four single restrictions, six pair restrictions and four triple restrictions
remain after two explicit endpoint premises: the complete raw response is
zero, and the quadruple intersection kills the kernel. Both premises must
be proved by the caller. No residual condition is silently imposed on h.

This module contains finite response algebra and counting l2 aggregation.
It has no physical labels, diffusion, MDS geometry or AES cap. Future source
only, outside the current double-uniform compile/acceptance inventory.
Constructive mathematics only; no attacks. Independent retained keys,
whitening, omitted final MixColumns, ordered-distinct reference pairs and
the fixed AES 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FourteenResponse
open AESMixing
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WeightedResponse (rawResponse zeroResponse)
open AESConcrete.TripleResponse (intersectionResponse)

section Definitions
variable {S Y V : Type*} [Fintype S]

def normalizer (V : Type*) [Fintype V] : ℝ :=
  (Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 4

theorem normalizer_nonneg (V : Type*) [Fintype V] : 0 ≤ normalizer V := by
  unfold normalizer
  positivity

theorem normalizer_eq (V : Type*) [Fintype V] (hn : 1 ≤ Fintype.card V) :
    normalizer V = ((Fintype.card V : ℝ) - 1) ^ 2 := by
  have hn' : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hq : 0 ≤ (Fintype.card V : ℝ) - 1 := by linarith
  calc
    _ = ((Real.sqrt ((Fintype.card V : ℝ) - 1)) ^ 2) ^ 2 := by
      unfold normalizer
      ring
    _ = _ := by rw [Real.sq_sqrt hq]

theorem normalizer_sq (V : Type*) [Fintype V] (hn : 1 ≤ Fintype.card V) :
    normalizer V ^ 2 = ((Fintype.card V : ℝ) - 1) ^ 4 := by
  rw [normalizer_eq V hn]
  ring

variable [AddCommGroup V] [Fintype V] [DecidableEq V]

def tripleIntersectionResponse (h : S → ℝ) (K : Y → S → ℝ)
    (a b c : S → V) (y : Y) : ℝ :=
  ∑ x, if a x = 0 ∧ b x = 0 ∧ c x = 0 then h x * K y x else 0

def quadrupleResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) (y : Y) : ℝ :=
  ∑ x, if c 0 x = 0 ∧ c 1 x = 0 ∧ c 2 x = 0 ∧ c 3 x = 0 then h x * K y x else 0

/-- Exactly four normalized weights, on the same finite source and signed h. -/
def weightedResponse (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) (y : Y) : ℝ :=
  ∑ x, h x * nonzeroUniform (c 0 x) * nonzeroUniform (c 1 x) *
    nonzeroUniform (c 2 x) * nonzeroUniform (c 3 x) * K y x

def singleResponses (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) : Fin 4 → Y → ℝ :=
  fun i => zeroResponse h K (c i)

/-- Lexicographic distinct pairs of the caller's four event labels. -/
def pairResponses (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) : Fin 6 → Y → ℝ :=
  ![intersectionResponse h K (c 0) (c 1), intersectionResponse h K (c 0) (c 2),
    intersectionResponse h K (c 0) (c 3), intersectionResponse h K (c 1) (c 2),
    intersectionResponse h K (c 1) (c 3), intersectionResponse h K (c 2) (c 3)]

/-- Lexicographic distinct triples; no triple restriction is discarded. -/
def tripleResponses (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) : Fin 4 → Y → ℝ :=
  ![tripleIntersectionResponse h K (c 0) (c 1) (c 2),
    tripleIntersectionResponse h K (c 0) (c 1) (c 3),
    tripleIntersectionResponse h K (c 0) (c 2) (c 3),
    tripleIntersectionResponse h K (c 1) (c 2) (c 3)]

end Definitions

/-- Signed numerator, separated from its normalization and source semantics. -/
def aggregate {Y : Type*} (A : Fin 4 → Y → ℝ) (B : Fin 6 → Y → ℝ)
    (C : Fin 4 → Y → ℝ) (y : Y) : ℝ :=
  -(∑ i : Fin 4, A i y) + (∑ i : Fin 6, B i y) - (∑ i : Fin 4, C i y)

section Identity
variable {S Y V : Type*} [Fintype S] [AddCommGroup V] [Fintype V] [DecidableEq V]

omit [Fintype S] in
private theorem weighted_summand (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) (y : Y) (x : S) :
    h x * nonzeroUniform (c 0 x) * nonzeroUniform (c 1 x) *
      nonzeroUniform (c 2 x) * nonzeroUniform (c 3 x) * K y x =
    (h x * K y x -
      (if c 0 x = 0 then h x * K y x else 0) -
      (if c 1 x = 0 then h x * K y x else 0) -
      (if c 2 x = 0 then h x * K y x else 0) -
      (if c 3 x = 0 then h x * K y x else 0) +
      (if c 0 x = 0 ∧ c 1 x = 0 then h x * K y x else 0) +
      (if c 0 x = 0 ∧ c 2 x = 0 then h x * K y x else 0) +
      (if c 0 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) +
      (if c 1 x = 0 ∧ c 2 x = 0 then h x * K y x else 0) +
      (if c 1 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) +
      (if c 2 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) -
      (if c 0 x = 0 ∧ c 1 x = 0 ∧ c 2 x = 0 then h x * K y x else 0) -
      (if c 0 x = 0 ∧ c 1 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) -
      (if c 0 x = 0 ∧ c 2 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) -
      (if c 1 x = 0 ∧ c 2 x = 0 ∧ c 3 x = 0 then h x * K y x else 0) +
      (if c 0 x = 0 ∧ c 1 x = 0 ∧ c 2 x = 0 ∧ c 3 x = 0 then h x * K y x else 0)) /
        normalizer V := by
  by_cases h0 : c 0 x = 0 <;> by_cases h1 : c 1 x = 0 <;>
    by_cases h2 : c 2 x = 0 <;> by_cases h3 : c 3 x = 0
  all_goals
    simp [nonzeroUniform, supportConstant, identityKernel, h0, h1, h2, h3,
      normalizer, div_eq_mul_inv]
    <;> ring_nf

/-- Complete sixteen-term inclusion-exclusion, before dropping either endpoint. -/
theorem weightedResponse_eq_sixteen (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) :
    weightedResponse h K c = fun y =>
      (rawResponse h K y + aggregate (singleResponses h K c) (pairResponses h K c)
        (tripleResponses h K c) y + quadrupleResponse h K c y) / normalizer V := by
  funext y
  unfold weightedResponse
  simp_rw [weighted_summand h K c y]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [aggregate, singleResponses, pairResponses, tripleResponses,
    rawResponse, zeroResponse, intersectionResponse, tripleIntersectionResponse,
    quadrupleResponse, Fin.sum_univ_succ]
  ring_nf

omit [Fintype V] in
theorem quadrupleResponse_zero_of_kernel (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V)
    (hquad : ∀ y x, c 0 x = 0 → c 1 x = 0 → c 2 x = 0 → c 3 x = 0 → K y x = 0) :
    quadrupleResponse h K c = 0 := by
  funext y
  unfold quadrupleResponse
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with hx
  · rw [hquad y x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2, mul_zero]
  · rfl

/-- The caller supplies both endpoint cancellations. All fourteen proper
nonempty intersections survive, regardless of signs or h at zero. -/
theorem weightedResponse_eq_fourteen (h : S → ℝ) (K : Y → S → ℝ)
    (c : Fin 4 → S → V) (hfull : rawResponse h K = 0)
    (hquad : ∀ y x, c 0 x = 0 → c 1 x = 0 → c 2 x = 0 → c 3 x = 0 → K y x = 0) :
    weightedResponse h K c = fun y =>
      aggregate (singleResponses h K c) (pairResponses h K c) (tripleResponses h K c) y /
        normalizer V := by
  rw [weightedResponse_eq_sixteen h K c, hfull, quadrupleResponse_zero_of_kernel h K c hquad]
  simp only [Pi.zero_apply, zero_add, add_zero]

end Identity

section CountingNorm
variable {Y Z : Type*} [Fintype Y] [Fintype Z]

/-- Four negative, six positive, then four negative response norms are added
before squaring; no output orthogonality premise is present. -/
theorem fourteen_response_l2 (A : Fin 4 → Y → ℝ) (B : Fin 6 → Y → ℝ)
    (C : Fin 4 → Y → ℝ) (d : ℝ) :
    l2 (fun y => aggregate A B C y / d) ≤
      ((∑ i, l2 (A i)) + (∑ i, l2 (B i)) + (∑ i, l2 (C i))) / |d| := by
  rw [WeightedResponse.l2_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg d)
  have hA : l2 (fun y => ∑ i : Fin 4, A i y) ≤ ∑ i, l2 (A i) :=
    l2_finset_sum_le Finset.univ A
  have hB : l2 (fun y => ∑ i : Fin 6, B i y) ≤ ∑ i, l2 (B i) :=
    l2_finset_sum_le Finset.univ B
  have hC : l2 (fun y => ∑ i : Fin 4, C i y) ≤ ∑ i, l2 (C i) :=
    l2_finset_sum_le Finset.univ C
  have he : aggregate A B C = fun y =>
      (∑ i : Fin 6, B i y) - (∑ i : Fin 4, A i y) - (∑ i : Fin 4, C i y) := by
    funext y
    unfold aggregate
    ring
  rw [he]
  have hab := (WeightedResponse.l2_sub_le
    (fun y => ∑ i : Fin 6, B i y) (fun y => ∑ i : Fin 4, A i y)).trans
      (add_le_add hB hA)
  exact ((WeightedResponse.l2_sub_le
    (fun y => (∑ i : Fin 6, B i y) - (∑ i : Fin 4, A i y))
    (fun y => ∑ i : Fin 4, C i y)).trans (add_le_add hab hC)).trans_eq (by ring)

/-- All categories are charged to one original input energy, with their own
norm coefficients and the exact multiplicities four, six and four. -/
theorem fourteen_response_l2_le (A : Fin 4 → Y → ℝ) (B : Fin 6 → Y → ℝ)
    (C : Fin 4 → Y → ℝ) (g : Z → ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ i, (∑ y, A i y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : ∀ i, (∑ y, B i y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : ∀ i, (∑ y, C i y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2) :
    l2 (fun y => aggregate A B C y / d) ≤
      ((4 * a + 6 * b + 4 * c) / |d|) * l2 g := by
  have hsumA : (∑ i, l2 (A i)) ≤ (4 * a) * l2 g := by
    calc
      _ ≤ ∑ _i : Fin 4, a * l2 g :=
        Finset.sum_le_sum (fun i _ => l2_le_of_energy (A i) g a ha (hA i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsumB : (∑ i, l2 (B i)) ≤ (6 * b) * l2 g := by
    calc
      _ ≤ ∑ _i : Fin 6, b * l2 g :=
        Finset.sum_le_sum (fun i _ => l2_le_of_energy (B i) g b hb (hB i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsumC : (∑ i, l2 (C i)) ≤ (4 * c) * l2 g := by
    calc
      _ ≤ ∑ _i : Fin 4, c * l2 g :=
        Finset.sum_le_sum (fun i _ => l2_le_of_energy (C i) g c hc (hC i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc
    _ ≤ ((∑ i, l2 (A i)) + (∑ i, l2 (B i)) + (∑ i, l2 (C i))) / |d| :=
      fourteen_response_l2 A B C d
    _ ≤ ((4 * a) * l2 g + (6 * b) * l2 g + (4 * c) * l2 g) / |d| :=
      div_le_div_of_nonneg_right (add_le_add (add_le_add hsumA hsumB) hsumC) (abs_nonneg d)
    _ = _ := by ring

end CountingNorm

section WeightedEnergy
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The fourteen norm estimates combine only after the exact endpoint
cancellations. Geometry, amplitude extraction and each energy cap are caller
obligations, so this theorem alone asserts no physical AES bound. -/
theorem weightedResponse_energy_le (hn : 1 ≤ Fintype.card V)
    (h : S → ℝ) (K : Y → S → ℝ) (events : Fin 4 → S → V) (g : Z → ℝ)
    (hfull : rawResponse h K = 0)
    (hquad : ∀ y x, events 0 x = 0 → events 1 x = 0 →
      events 2 x = 0 → events 3 x = 0 → K y x = 0)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ i, (∑ y, singleResponses h K events i y ^ 2) ≤ a ^ 2 * ∑ z, g z ^ 2)
    (hB : ∀ i, (∑ y, pairResponses h K events i y ^ 2) ≤ b ^ 2 * ∑ z, g z ^ 2)
    (hC : ∀ i, (∑ y, tripleResponses h K events i y ^ 2) ≤ c ^ 2 * ∑ z, g z ^ 2) :
    (∑ y, weightedResponse h K events y ^ 2) ≤
      ((4 * a + 6 * b + 4 * c) ^ 2 / ((Fintype.card V : ℝ) - 1) ^ 4) *
        ∑ z, g z ^ 2 := by
  have hl := fourteen_response_l2_le (singleResponses h K events) (pairResponses h K events)
    (tripleResponses h K events) g a b c (normalizer V) ha hb hc hA hB hC
  rw [← weightedResponse_eq_fourteen h K events hfull hquad] at hl
  rw [abs_of_nonneg (normalizer_nonneg V)] at hl
  have hcoef : 0 ≤ (4 * a + 6 * b + 4 * c) / normalizer V :=
    div_nonneg (by positivity) (normalizer_nonneg V)
  have hs := (sq_le_sq₀ (l2_nonneg (weightedResponse h K events))
    (mul_nonneg hcoef (l2_nonneg g))).mpr hl
  simpa only [mul_pow, l2_sq, div_pow, normalizer_sq V hn] using hs

end WeightedEnergy
end AESConcrete.FourteenResponse
