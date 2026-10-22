/- Module role: Concrete source bounds and startup estimates for the historical profile.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Source.Startup
import AESConcrete.ActualWordMoments

/-!
# Exact one-source high-degree lengths

Retain the ordinary source atom coefficient `79/4`, the exact squared Gram
table total `8974717/100`, and the sharp centered column coefficient
`2/15 - 1/(q-1)`. The existing common-source proof is parameterized by these
resources; no independent-current-coordinate hypothesis is introduced.

This module supplies only actual one-source degree/component lengths.
Sharp physical step estimates and the first-high scalar composition are
separate consumers. Parent-owned formal compilation is required. Constructive
proofs only; no attacks, manuscript edits, or predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.SharpOneSourceLengths
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESPaper.OneSourceResidual (R)
open AESPaper.OneSourceEnergies (G)
open DegreeHilbertSchmidt (block block_hs_pythagoras)
open HilbertSchmidtEnergy (hs hs_sq hs_nonneg)

def atomCoeff : ℝ := 79 / 4
def gramCoeffSq : ℝ := 8974717 / 100
def diagonalCoeff : ℝ := 2 / 15 - 1 / (q - 1)
def columnCap : ℝ := diagonalCoeff / q
def gramLength : ℝ := Real.sqrt gramCoeffSq / q

def degreeThreeBudget : ℝ :=
  4 * atomCoeff ^ 2 * gramCoeffSq * diagonalCoeff / (q - 1)

def degreeFourBudget : ℝ :=
  atomCoeff ^ 2 * gramCoeffSq * diagonalCoeff ^ 2 / q

-- The parent supplied these exact rational enclosures after its separate
-- formal-node screen. They are re-proved from the resource formulas below.
def degreeThreeLength : ℝ := 659321008722873 / 10000000000000000
def degreeFourLength : ℝ := 30093749063103 / 2500000000000000

theorem columnCap_nonneg : 0 ≤ columnCap := by
  norm_num [columnCap, diagonalCoeff, q]

theorem gramLength_sq : gramLength ^ 2 = gramCoeffSq / q ^ 2 := by
  unfold gramLength
  rw [div_pow, Real.sq_sqrt (by norm_num [gramCoeffSq])]

section ExactResources

theorem source_atom_le (a x : AES.Word) (ha : a ≠ 0) :
    |wordLaw a x| ≤ atomCoeff / q := by
  rw [abs_of_nonneg (AESPaper.StartingWord.wordLaw_nonnegative a x)]
  calc
    _ ≤ ByteFifthMoments.ddtMoment :=
      AESPaper.StartingWord.wordLaw_point_le_fifth a x ha
    _ = atomCoeff / q := by
      norm_num [ByteFifthMoments.ddtMoment, atomCoeff, q]

/-- The nonzero-column theorem needs this separate zero-column case. -/
theorem residual_zero_column (y : AES.Word) : R y 0 = 0 := by
  unfold AESPaper.OneSourceResidual.R residualMatrix
  rw [AES.word_superbox_pointed.zero_column]
  by_cases hy : y = 0 <;> simp [activityMatrix, hy]

/-- Uniform diagonal cap, including the distinguished source column. -/
theorem residual_column_le (x : AES.Word) : gram R x x ≤ columnCap := by
  by_cases hx : x = 0
  · subst x
    simpa only [gram, residual_zero_column, zero_mul, Finset.sum_const_zero] using
      columnCap_nonneg
  · have h := (AESPaper.StartingWord.residual_column_energy_lt_sharp x hx).le
    have hc : 17 / (15 * q) - 1 / (q - 1) = columnCap := by
      norm_num [columnCap, diagonalCoeff, q]
    rw [hc] at h
    simpa only [gram, AESPaper.OneSourceResidual.R, pow_two] using h

/-- Stop the inherited orthogonal Gram assembly before rounding its exact
table total upward to `300^2`. No new HS premise is left in this wrapper. -/
theorem residual_gram_moment_le :
    (∑ x, ∑ z, gram R x z ^ 2) ≤ gramCoeffSq / q ^ 2 := by
  change (∑ x, ∑ z,
    gram (WordMomentAssembly.residual .ordinary .ordinary false) x z ^ 2) ≤ _
  rw [← hs_sq]
  rw [← block_hs_pythagoras (0 : BinaryWord 8) (by norm_num [BinaryWord.card])]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5,
        (WordMomentNumbers.gramCap i j / 4294967296) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (hs_nonneg _)
        (WordMomentAssembly.gram_block_lt_of_degree_bounds .ordinary .ordinary false
          (ActualWordMoments.actual_degree_hs_bounds .ordinary .ordinary false) i j).le 2
    _ = (∑ i : Fin 5, ∑ j : Fin 5, WordMomentNumbers.gramCap i j ^ 2) /
        (4294967296 : ℝ) ^ 2 := by
      simp only [div_pow, Finset.sum_div]
    _ = gramCoeffSq / q ^ 2 := by
      rw [WordMomentNumbers.gram_total]
      norm_num [gramCoeffSq, q]

theorem source_gram_entry_le (k i : Fin 4) (x z : AES.Word) :
    |G k i x z| ≤ columnCap :=
  gram_entry_bound R columnCap columnCap_nonneg residual_column_le _ _

/-- Source permutations preserve the whole second moment, not individual entries. -/
theorem source_gram_moment_le (k i : Fin 4) :
    (∑ x, ∑ z, G k i x z ^ 2) ≤ gramLength ^ 2 := by
  change (∑ x, ∑ z, gram R (AESPaper.BoundarySourceCoordinates.outputEquiv k i x)
    (AESPaper.BoundarySourceCoordinates.outputEquiv k i z) ^ 2) ≤ _
  rw [AESPaper.CappedSourceGram.gram_moment_relabel, gramLength_sq]
  exact residual_gram_moment_le

end ExactResources

section LawEnergy

theorem pattern_high_energy_le (b : Fin 4 → Bool) (hb : 2 ≤ residualDegree b)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, action (productProjection (0 : AES.Word) b)
      (AESPaper.OneSourceLaw.law k a) y ^ 2) ≤
      (atomCoeff / q) ^ 2 * gramLength ^ 2 * columnCap ^ (residualDegree b - 2) *
        (1 / (q - 1)) ^ (4 - residualDegree b) := by
  rw [AESPaper.OneSourceEnergies.pattern_energy b k a ha]
  exact AESPaper.FourSourcePattern.mixed_bound (G k) (wordLaw a)
    (atomCoeff / q) gramLength columnCap (1 / (q - 1))
    (by norm_num [atomCoeff, q]) columnCap_nonneg (by norm_num [q])
    (fun x => source_atom_le a x ha) (source_gram_entry_le k)
    (source_gram_moment_le k) b hb

/-- Orthogonality retains the exact binomial multiplicity. -/
theorem degree_high_energy_le (j : Fin 5) (hj : 2 ≤ j.val)
    (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, degreeComponent (0 : AES.Word) j (AESPaper.OneSourceLaw.law k a) y ^ 2) ≤
      (Nat.choose 4 j.val : ℝ) * ((atomCoeff / q) ^ 2 * gramLength ^ 2 *
        columnCap ^ (j.val - 2) * (1 / (q - 1)) ^ (4 - j.val)) := by
  apply AESPaper.OneSourceBounds.degree_energy_of_pattern_le
  intro b hb
  have hd : residualDegree b = j.val := congrArg Fin.val hb
  simpa only [hd] using pattern_high_energy_le b (by omega) k a ha

end LawEnergy

section ActualInput

theorem actual_degree_high_energy_le (b : AES.State) (hb : activeSourceCount b = 1)
    (j : Fin 5) (hj : 2 ≤ j.val) :
    (∑ y, degreeComponent (0 : AES.Word) j (error 1 b) y ^ 2) ≤
      (Nat.choose 4 j.val : ℝ) * ((atomCoeff / q) ^ 2 * gramLength ^ 2 *
        columnCap ^ (j.val - 2) * (1 / (q - 1)) ^ (4 - j.val)) := by
  obtain ⟨k, a, ha, hsource⟩ := AESPaper.UniversalInitialization.one_active_source b hb
  have hj0 : j ≠ 0 := by
    intro h0
    have hv := congrArg Fin.val h0
    change j.val = 0 at hv
    omega
  have herr : error 1 b =
      AESPaper.OneSourceLaw.law k a - uniformExcept (0 : AES.WordState) := by
    change AESPaper.GroupedLaw.groupedLaw 1 b - uniformExcept (0 : AES.WordState) = _
    rw [AESPaper.OneSourceLaw.groupedLaw_one_eq_law b k a hsource]
  rw [herr, AESPaper.OneSourceEnergies.centered_positive_degree j hj0 k a]
  exact degree_high_energy_le j hj k a ha

theorem actual_degree_three_scaled_energy_le (b : AES.State)
    (hb : activeSourceCount b = 1) :
    q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) (3 : Fin 5) (error 1 b) y ^ 2) ≤
      degreeThreeBudget := by
  calc
    _ ≤ q ^ 5 * ((Nat.choose 4 3 : ℝ) * ((atomCoeff / q) ^ 2 * gramLength ^ 2 *
        columnCap ^ (3 - 2) * (1 / (q - 1)) ^ (4 - 3))) :=
      mul_le_mul_of_nonneg_left (actual_degree_high_energy_le b hb 3 (by decide))
        (by norm_num [q])
    _ = degreeThreeBudget := by
      rw [gramLength_sq]
      norm_num [degreeThreeBudget, atomCoeff, gramCoeffSq, columnCap, diagonalCoeff, q,
        Nat.choose]

theorem actual_degree_four_scaled_energy_le (b : AES.State)
    (hb : activeSourceCount b = 1) :
    q ^ 5 * (∑ y, degreeComponent (0 : AES.Word) (4 : Fin 5) (error 1 b) y ^ 2) ≤
      degreeFourBudget := by
  calc
    _ ≤ q ^ 5 * ((Nat.choose 4 4 : ℝ) * ((atomCoeff / q) ^ 2 * gramLength ^ 2 *
        columnCap ^ (4 - 2) * (1 / (q - 1)) ^ (4 - 4))) :=
      mul_le_mul_of_nonneg_left (actual_degree_high_energy_le b hb 4 (by decide))
        (by norm_num [q])
    _ = degreeFourBudget := by
      rw [gramLength_sq]
      norm_num [degreeFourBudget, atomCoeff, gramCoeffSq, columnCap, diagonalCoeff, q,
        Nat.choose]

theorem degree_three_budget_le_length_sq : degreeThreeBudget ≤ degreeThreeLength ^ 2 := by
  norm_num [degreeThreeBudget, degreeThreeLength, atomCoeff, gramCoeffSq, diagonalCoeff, q]

theorem degree_four_budget_le_length_sq : degreeFourBudget ≤ degreeFourLength ^ 2 := by
  norm_num [degreeFourBudget, degreeFourLength, atomCoeff, gramCoeffSq, diagonalCoeff, q]

private theorem scaled_length_of_energy (f : AES.WordState → ℝ) {C c : ℝ}
    (hc : 0 ≤ c) (he : q ^ 5 * (∑ x, f x ^ 2) ≤ C) (hC : C ≤ c ^ 2) :
    (2 : ℝ) ^ (80 : ℕ) * l2 f ≤ c := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) hc).mp
  calc
    ((2 : ℝ) ^ (80 : ℕ) * l2 f) ^ 2 = q ^ 5 * (∑ x, f x ^ 2) := by
      rw [mul_pow, l2_sq]
      norm_num [q]
    _ ≤ C := he
    _ ≤ c ^ 2 := hC

theorem scaled_degree_three_le (b : AES.State) (hb : activeSourceCount b = 1) :
    (2 : ℝ) ^ (80 : ℕ) *
      l2 (degreeComponent (0 : AES.Word) (3 : Fin 5) (error 1 b)) ≤
        659321008722873 / 10000000000000000 :=
  scaled_length_of_energy _ (by norm_num [degreeThreeLength])
    (actual_degree_three_scaled_energy_le b hb) degree_three_budget_le_length_sq

theorem scaled_degree_four_le (b : AES.State) (hb : activeSourceCount b = 1) :
    (2 : ℝ) ^ (80 : ℕ) *
      l2 (degreeComponent (0 : AES.Word) (4 : Fin 5) (error 1 b)) ≤
        30093749063103 / 2500000000000000 :=
  scaled_length_of_energy _ (by norm_num [degreeFourLength])
    (actual_degree_four_scaled_energy_le b hb) degree_four_budget_le_length_sq

end ActualInput
end AES8.SharpOneSourceLengths
