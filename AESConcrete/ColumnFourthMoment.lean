import AESConcrete.ByteGramResources
import AESMixing.Gram

/-!
# Weighted fourth moments for the single-active-byte column bound

The label type below is the nonzero source-label space, not a byte space
containing a zero label with a different Gram diagonal.  The application may
instantiate it with `NonzeroByte` after proving the required relabelings.

This module separates three responsibilities: signed Gram entries bound
moments two through four; an explicitly supplied first-moment bound controls
the linear term; a pointwise four-factor inequality combines four full Grams.
The exact AES rational comparison is arithmetic only.  No actual word-column
identity, centered-source energy estimate, or MDS geometry is assumed proved
by this module. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ColumnFourthMoment

variable {V : Type*} [Fintype V] [DecidableEq V]

def weightedMoment (μ : V → ℝ) (G : V → V → ℝ) (k : ℕ) : ℝ :=
  ∑ x, ∑ y, μ x * μ y * G x y ^ k

theorem pair_mass (μ : V → ℝ) (hmass : (∑ x, μ x) = 1) :
    (∑ x, ∑ y, μ x * μ y) = 1 := by
  simp_rw [← Finset.mul_sum, hmass, mul_one]
  exact hmass

/-- The diagonal and distinct-label weights are exactly ρ and 1-ρ. -/
theorem weighted_diagonal_split (μ : V → ℝ) (ρ a b : ℝ)
    (hmass : (∑ x, μ x) = 1) (hcollision : (∑ x, μ x ^ 2) = ρ) :
    (∑ x, ∑ y, μ x * μ y * (if x = y then a else b)) =
      ρ * a + (1 - ρ) * b := by
  have hp (x y : V) :
      μ x * μ y * (if x = y then a else b) =
        b * (μ x * μ y) + (if y = x then (a - b) * μ x ^ 2 else 0) := by
    by_cases h : x = y
    · subst y
      simp only [ite_true]
      ring
    · simp only [if_neg h, if_neg (Ne.symm h)]
      ring
  have hbase : (∑ x, ∑ y, b * (μ x * μ y)) = b := by
    calc
      _ = b * (∑ x, ∑ y, μ x * μ y) := by simp_rw [Finset.mul_sum]
      _ = b := by rw [pair_mass μ hmass, mul_one]
  have hdiag : (∑ x, ∑ y, if y = x then (a - b) * μ x ^ 2 else 0) =
      (a - b) * ρ := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_sum, hcollision]
  calc
    _ = (∑ x, ∑ y, b * (μ x * μ y)) +
        (∑ x, ∑ y, if y = x then (a - b) * μ x ^ 2 else 0) := by
      simp only [hp, Finset.sum_add_distrib]
    _ = _ := by rw [hbase, hdiag]; ring

theorem weightedMoment_le (μ : V → ℝ) (G : V → V → ℝ) (k : ℕ) (ρ a b : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : (∑ x, μ x) = 1)
    (hcollision : (∑ x, μ x ^ 2) = ρ)
    (hdiag : ∀ x, G x x ^ k = a)
    (hoff : ∀ x y, x ≠ y → G x y ^ k ≤ b) :
    weightedMoment μ G k ≤ ρ * a + (1 - ρ) * b := by
  rw [← weighted_diagonal_split μ ρ a b hmass hcollision]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hμ x) (hμ y))
  by_cases h : x = y
  · subst y
    rw [if_pos rfl, hdiag]
  · rw [if_neg h]
    exact hoff x y h

/-- Signed entry information alone controls the three nonlinear moments. -/
theorem signed_moments (μ : V → ℝ) (G : V → V → ℝ) (ρ Δ gminus gplus : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : (∑ x, μ x) = 1)
    (hcollision : (∑ x, μ x ^ 2) = ρ)
    (hminus : 0 ≤ gminus) (hplus : gplus ≤ gminus)
    (hdiag : ∀ x, G x x = Δ)
    (hoff : ∀ x y, x ≠ y → -gminus ≤ G x y ∧ G x y ≤ gplus) :
    weightedMoment μ G 2 ≤ ρ * Δ ^ 2 + (1 - ρ) * gminus ^ 2 ∧
    weightedMoment μ G 3 ≤ ρ * Δ ^ 3 + (1 - ρ) * gplus ^ 3 ∧
    weightedMoment μ G 4 ≤ ρ * Δ ^ 4 + (1 - ρ) * gminus ^ 4 := by
  have hsquare (x y : V) (hxy : x ≠ y) : G x y ^ 2 ≤ gminus ^ 2 := by
    rcases hoff x y hxy with ⟨hl, hu⟩
    have hu' := le_trans hu hplus
    have hp := mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hl)
    nlinarith
  refine ⟨weightedMoment_le μ G 2 ρ (Δ ^ 2) (gminus ^ 2)
    hμ hmass hcollision (fun x => by rw [hdiag]) hsquare, ?_, ?_⟩
  · apply weightedMoment_le μ G 3 ρ (Δ ^ 3) (gplus ^ 3) hμ hmass hcollision
      (fun x => by rw [hdiag])
    intro x y hxy
    exact (Odd.pow_le_pow (show Odd 3 by decide)).2 (hoff x y hxy).2
  · apply weightedMoment_le μ G 4 ρ (Δ ^ 4) (gminus ^ 4) hμ hmass hcollision
      (fun x => by rw [hdiag])
    intro x y hxy
    have hp := mul_nonneg (sub_nonneg.mpr (hsquare x y hxy))
      (add_nonneg (sq_nonneg gminus) (sq_nonneg (G x y)))
    nlinarith

def fourthBound (c ν ρ Δ gminus gplus : ℝ) : ℝ :=
  c ^ 4 + 4 * c ^ 3 * (ν ^ 2 * Δ) +
    6 * c ^ 2 * (ρ * Δ ^ 2 + (1 - ρ) * gminus ^ 2) +
    4 * c * (ρ * Δ ^ 3 + (1 - ρ) * gplus ^ 3) +
    (ρ * Δ ^ 4 + (1 - ρ) * gminus ^ 4)

theorem full_fourth_expansion (μ : V → ℝ) (G : V → V → ℝ) (c : ℝ)
    (hmass : (∑ x, μ x) = 1) :
    weightedMoment μ (fun x y => c + G x y) 4 =
      c ^ 4 + 4 * c ^ 3 * weightedMoment μ G 1 +
        6 * c ^ 2 * weightedMoment μ G 2 +
        4 * c * weightedMoment μ G 3 + weightedMoment μ G 4 := by
  have hp (x y : V) : μ x * μ y * (c + G x y) ^ 4 =
      c ^ 4 * (μ x * μ y) + 4 * c ^ 3 * (μ x * μ y * G x y ^ 1) +
        6 * c ^ 2 * (μ x * μ y * G x y ^ 2) +
        4 * c * (μ x * μ y * G x y ^ 3) + μ x * μ y * G x y ^ 4 := by ring
  simp only [weightedMoment, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hmass, mul_one]

/-- The first moment is a separate hypothesis. In the concrete application
it must come from the actual residual energy of the centered source law. -/
theorem full_fourth_moment_le (μ : V → ℝ) (G : V → V → ℝ)
    (c ν ρ Δ gminus gplus : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : (∑ x, μ x) = 1)
    (hcollision : (∑ x, μ x ^ 2) = ρ) (hc : 0 ≤ c)
    (hminus : 0 ≤ gminus) (hplus : gplus ≤ gminus)
    (hdiag : ∀ x, G x x = Δ)
    (hoff : ∀ x y, x ≠ y → -gminus ≤ G x y ∧ G x y ≤ gplus)
    (hfirst : weightedMoment μ G 1 ≤ ν ^ 2 * Δ) :
    weightedMoment μ (fun x y => c + G x y) 4 ≤
      fourthBound c ν ρ Δ gminus gplus := by
  rcases signed_moments μ G ρ Δ gminus gplus hμ hmass hcollision
    hminus hplus hdiag hoff with ⟨h2, h3, h4⟩
  rw [full_fourth_expansion μ G c hmass]
  unfold fourthBound
  have h1' := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 4 * c ^ 3)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 6 * c ^ 2)
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * c)
  linarith

/-- A fourth-power comparison without roots or a positivity hypothesis on
the four factors. Its weighted application needs nonnegative weights. -/
theorem four_mul_le_fourth_sum (a b c d : ℝ) :
    4 * (a * b * c * d) ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
    sq_nonneg (a * b - c * d)]

theorem weighted_four_product_le (μ : V → ℝ)
    (A B C D : V → V → ℝ) (K : ℝ)
    (hμ : ∀ x, 0 ≤ μ x)
    (hA : weightedMoment μ A 4 ≤ K) (hB : weightedMoment μ B 4 ≤ K)
    (hC : weightedMoment μ C 4 ≤ K) (hD : weightedMoment μ D 4 ≤ K) :
    (∑ x, ∑ y, μ x * μ y * (A x y * B x y * C x y * D x y)) ≤ K := by
  have hp (x y : V) :
      μ x * μ y * (4 * (A x y * B x y * C x y * D x y)) ≤
        μ x * μ y * (A x y ^ 4 + B x y ^ 4 + C x y ^ 4 + D x y ^ 4) :=
    mul_le_mul_of_nonneg_left (four_mul_le_fourth_sum _ _ _ _)
      (mul_nonneg (hμ x) (hμ y))
  have hs := Finset.sum_le_sum (fun (x : V) (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (y : V) (_ : y ∈ Finset.univ) => hp x y))
  have he : (∑ x, ∑ y, μ x * μ y * (4 * (A x y * B x y * C x y * D x y))) =
      4 * (∑ x, ∑ y, μ x * μ y * (A x y * B x y * C x y * D x y)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he] at hs
  simp only [mul_add, Finset.sum_add_distrib] at hs
  change 4 * (∑ x, ∑ y, μ x * μ y * (A x y * B x y * C x y * D x y)) ≤
    weightedMoment μ A 4 + weightedMoment μ B 4 +
      weightedMoment μ C 4 + weightedMoment μ D 4 at hs
  linarith

def aesFourthBound : ℝ :=
  fourthBound (1 / 255) (9 / 128) (65 / 8192) (16766 / 4177920)
    (319 / 4177920) (191 / 4177920)

/-- Exact arithmetic from the source's single-active-byte column row. -/
theorem aesFourthBound_scaled_lt :
    (4294967296 : ℝ) * aesFourthBound < 1133 / 1000 := by
  norm_num [aesFourthBound, fourthBound]

theorem aesFourthBound_lt : aesFourthBound < (17 / (15 * 4294967296) : ℝ) := by
  have h := aesFourthBound_scaled_lt
  nlinarith

end AESConcrete.ColumnFourthMoment
