import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Exact scalar slack for the direct return (13,12) argument

This component contains only the square-root normalization and exact
comparisons with the frozen L,J and lambda. Operator identities, signed
response estimates and support aggregation remain distinct analytic
obligations.

Constructive fixed AES10/14/16: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.

This scalar module has no dependency on the ReturnMiddle modules.
-/

noncomputable section

namespace AESConcrete.Return13_12Scalar
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L J)

set_option maxRecDepth 100000

/-- Three normalized nonzero-uniform factors occur in the direct composition. -/
def normalizationRatio : ℝ := 65537 / Real.sqrt (q - 1)
def normalizationCube : ℝ := normalizationRatio ^ 3

/-- These are the unchanged certificate data, not asserted operator norms. -/
def a : ℝ := lambda * L 13 11
def b : ℝ := lambda * L 13 12
def c : ℝ := lambda * L 11 12
def T : ℝ := lambda ^ 2 * J 13 12

/-- Factor8 belongs to the separately proved support aggregation. This file
compares the resulting number without asserting that analytic implication. -/
def B : ℝ := 8 * rho ^ 5 * kappa * normalizationCube
def Delta : ℝ := T - a * c - rho ^ 4 * b

theorem normalizationRatio_nonneg : 0 ≤ normalizationRatio :=
  div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem normalizationCube_nonneg : 0 ≤ normalizationCube :=
  pow_nonneg normalizationRatio_nonneg 3

/-- Keep the irrational denominator exact before a separate rational bound. -/
theorem normalizationRatio_sq :
    normalizationRatio ^ 2 = (65537 : ℝ) / 65535 := by
  unfold normalizationRatio
  rw [div_pow, Real.sq_sqrt (le_of_lt q_sub_one_pos)]
  norm_num [q]

theorem normalizationCube_sq :
    normalizationCube ^ 2 = ((65537 : ℝ) / 65535) ^ 3 := by
  unfold normalizationCube
  rw [show (normalizationRatio ^ 3) ^ 2 =
      (normalizationRatio ^ 2) ^ 3 by ring, normalizationRatio_sq]

theorem normalizationCube_lt : normalizationCube < (10001 : ℝ) / 10000 := by
  have hs : normalizationCube ^ 2 < ((10001 : ℝ) / 10000) ^ 2 := by
    rw [normalizationCube_sq]
    norm_num
  exact (sq_lt_sq₀ normalizationCube_nonneg (by norm_num)).mp hs

theorem leading_coefficient_pos : 0 < 8 * rho ^ 5 * kappa := by
  norm_num [rho, kappa]

theorem B_nonneg : 0 ≤ B :=
  mul_nonneg (le_of_lt leading_coefficient_pos) normalizationCube_nonneg

theorem T_pos : 0 < T := by
  norm_num [T, AESRound.Terminal.lambda, AESRound.Certificate.J]

/-- Exact requested constants, including 2^32-1 inside the square root. -/
theorem B_eq_concrete :
    B = 8 * (21 / 131072 : ℝ) ^ 5 * (2 / (15 * (2 : ℝ) ^ 32)) *
      ((65537 : ℝ) / Real.sqrt ((2 : ℝ) ^ 32 - 1)) ^ 3 := by
  norm_num [B, normalizationCube, normalizationRatio, rho, kappa, q]

theorem T_eq_rational :
    T = (1045178789081859 : ℝ) / ((2 : ℝ) ^ 96 * 500000000000000) := by
  norm_num [T, AESRound.Terminal.lambda, AESRound.Certificate.J]

theorem leading_coefficient_eq_rational :
    8 * rho ^ 5 * kappa = (4084101 : ℝ) / (15 * (2 : ℝ) ^ 113) := by
  norm_num [rho, kappa]

/-- Rational comparison after replacing only the normalization cube. -/
theorem leading_rational_bound :
    (8 * rho ^ 5 * kappa) * ((10001 : ℝ) / 10000) <
      ((199 : ℝ) / 200) * T := by
  norm_num [rho, kappa, T, AESRound.Terminal.lambda, AESRound.Certificate.J]

theorem B_lt_target_fraction : B < ((199 : ℝ) / 200) * T := by
  exact (mul_lt_mul_of_pos_left normalizationCube_lt leading_coefficient_pos).trans
    leading_rational_bound

/-- Both remaining high paths retain their actual frozen certificate entries. -/
theorem side_paths_lt_target_fraction :
    a * c + rho ^ 4 * b < ((1 : ℝ) / 500) * T := by
  norm_num [a, b, c, T, rho, AESRound.Terminal.lambda,
    AESRound.Certificate.L, AESRound.Certificate.J]

theorem return_scalar_lt_fraction :
    B + a * c + rho ^ 4 * b < ((997 : ℝ) / 1000) * T := by
  calc
    B + a * c + rho ^ 4 * b = B + (a * c + rho ^ 4 * b) := by ring
    _ < ((199 : ℝ) / 200) * T + ((1 : ℝ) / 500) * T :=
      add_lt_add B_lt_target_fraction side_paths_lt_target_fraction
    _ = ((997 : ℝ) / 1000) * T := by ring

theorem target_fraction_lt : ((997 : ℝ) / 1000) * T < T := by
  calc
    ((997 : ℝ) / 1000) * T < 1 * T :=
      mul_lt_mul_of_pos_right (by norm_num) T_pos
    _ = T := one_mul T

/-- The complete scalar inequality only; no physical return theorem is claimed. -/
theorem return_scalar_lt : B + a * c + rho ^ 4 * b < T :=
  return_scalar_lt_fraction.trans target_fraction_lt

theorem B_lt_Delta : B < Delta := by
  unfold Delta
  linarith [return_scalar_lt]

theorem Delta_pos : 0 < Delta := lt_of_le_of_lt B_nonneg B_lt_Delta

end AESConcrete.Return13_12Scalar
