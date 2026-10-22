import AESConcrete.ResidualIncidenceCoefficient
import AESConcrete.RefinedStepZeros
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Scalar certificates for the multi-uniform graph bound

The rational norm envelope preserves every even power of the known column
energy coefficient `kappa`; only an odd remaining column-norm power uses
`chi`. One `chi = 11 / (30 * 65536)` serves all three candidate columns.
The binomial numerator and the selected-support multiplicity are distinct:
the former aggregates expansion terms, and the latter aggregates orthogonal
input pieces by output Cauchy--Schwarz. No output orthogonality is assumed.

These scalar statements do not establish physical operator caps. Those
proofs belong to `UniformGraphCaps`; inventory composition belongs to
`UniformGraphStepCaps`. Constructive mathematics only; no attacks, workloads,
historical or manuscript edits. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and the 10/14/16 target stay
fixed. No return, initialization or complete AES theorem is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.UniformGraphScalar
open AESConcrete.RefinedStepZeros (blockType)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

set_option maxRecDepth 100000

def rho : ℝ := 21 / 131072
def kappa : ℝ := 2 / (15 * 4294967296)
def chi : ℝ := 11 / (30 * 65536)

theorem rho_nonneg : 0 ≤ rho := by norm_num [rho]
theorem kappa_nonneg : 0 ≤ kappa := by norm_num [kappa]
theorem chi_nonneg : 0 ≤ chi := by norm_num [chi]

/-- Exact rational domination of one odd column-norm factor. -/
theorem kappa_le_chi_sq : kappa ≤ chi ^ 2 := by
  norm_num [kappa, chi]

/-- Select either the ordinary or Fourier dimension, without comparing
their coefficients by monotonicity. -/
def safeGraphDim (e t : ℕ) : ℕ := min (e + t) (4 - t)

theorem safeGraphDim_le_four (e t : ℕ) : safeGraphDim e t ≤ 4 := by
  unfold safeGraphDim
  omega

/-- A rational norm cap, retaining exact even powers of `kappa`. -/
def safeGraphNorm (m : ℕ) : ℝ :=
  rho ^ m * kappa ^ ((4 - m) / 2) * chi ^ ((4 - m) % 2)

theorem safeGraphNorm_nonneg (m : ℕ) : 0 ≤ safeGraphNorm m := by
  unfold safeGraphNorm rho kappa chi
  positivity

/-- The underlying graph energy coefficient is dominated by the rational
norm cap. Only the five possible graph dimensions are evaluated. -/
theorem graphEnergy_le_safeGraphNorm_sq (m : ℕ) (hm : m ≤ 4) :
    rho ^ (2 * m) * kappa ^ (4 - m) ≤ safeGraphNorm m ^ 2 := by
  interval_cases m <;> norm_num [safeGraphNorm, rho, kappa, chi]

/-- The expansion coefficient before its exact square-root denominator. -/
def numerator (e k : ℕ) : ℝ :=
  ∑ t : Fin (k + 1),
    (Nat.choose k t.val : ℝ) * (65536 : ℝ) ^ t.val *
      safeGraphNorm (safeGraphDim e t.val)

theorem numerator_nonneg (e k : ℕ) : 0 ≤ numerator e k := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (safeGraphNorm_nonneg _)

/-- Counting-energy coefficient after exact support-piece aggregation.
The denominator is the square of `sqrt(q-1)^k`, including odd `k`. -/
def squaredBound (e b : Fin 5) : ℝ :=
  (ResidualIncidenceCoefficient.multiplicity e b : ℝ) *
    numerator e.val (b.val - e.val) ^ 2 /
      (4294967295 : ℝ) ^ (b.val - e.val)

abbrev graphSquaredBound := squaredBound

theorem squaredBound_nonneg (e b : Fin 5) : 0 ≤ squaredBound e b := by
  unfold squaredBound
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (by positivity)

/-- The three columns screened with this one rational odd-power envelope. -/
def uniformColumn (j : Fin 14) : Prop := j = 6 ∨ j = 7 ∨ j = 10

instance (j : Fin 14) : Decidable (uniformColumn j) := by
  unfold uniformColumn
  infer_instance

/-- The actual certificate order gives `(e,b) = (1,3), (1,4), (2,4)`. -/
theorem uniformColumn_blockType (j : Fin 14) (h : uniformColumn j) :
    blockType j = (1, 3) ∨ blockType j = (1, 4) ∨ blockType j = (2, 4) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Exact rational comparisons with the unchanged certificate entries.
They are deliberately separate from the operator and energy arguments. -/
theorem certificate_uniform_bounds (j : Fin 14) (h : uniformColumn j) :
    0 ≤ lambda * L 13 j ∧
      squaredBound (blockType j).1 (blockType j).2 ≤ (lambda * L 13 j) ^ 2 := by
  -- Enumerate concrete Fin constructors before evaluating the fixed sums.
  fin_cases j
  all_goals first
    | (exfalso; revert h; decide)
    | (norm_num [squaredBound, ResidualIncidenceCoefficient.multiplicity,
        Nat.choose, blockType, AESRound.Terminal.lambda, AESRound.Certificate.L]
       unfold numerator
       first | rw [Fin.sum_univ_three] | rw [Fin.sum_univ_four]
       norm_num [safeGraphDim, safeGraphNorm, rho, kappa, chi, Nat.choose])

end AESConcrete.UniformGraphScalar
