/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Fiber cardinalities and the paper's real-power normalization

These exact identities convert the two square-root denominators for fibers
of cardinalities `q^a` and `q^b` into `q^(-(a+b)/2)`. They are symbolic
identities, with no AES constants or numerical estimates.
-/

noncomputable section

namespace AES8.FiberNormalization

/-- The product of the two square roots in the normalized indicator maps. -/
theorem sqrt_pow_product (q a b : ℕ) :
    Real.sqrt ((q ^ a : ℕ) : ℝ) * Real.sqrt ((q ^ b : ℕ) : ℝ) =
      (q : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg (q ^ a)), ← Nat.cast_mul, ← pow_add,
    Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q)]
  congr 1
  ring

/-- Exact reciprocal normalization, including zero-dimensional fibers. -/
theorem inverse_sqrt_pow_product (q a b : ℕ) :
    1 / (Real.sqrt ((q ^ a : ℕ) : ℝ) * Real.sqrt ((q ^ b : ℕ) : ℝ)) =
      (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) := by
  rw [sqrt_pow_product, one_div]
  rw [show -(((a + b : ℕ) : ℝ)) / 2 = -(((a + b : ℕ) : ℝ) / 2) by ring,
    Real.rpow_neg (Nat.cast_nonneg q)]

/-- The coefficient in the manuscript is the same square-root denominator. -/
theorem div_sqrt_pow_product (q a b : ℕ) (s : ℝ) :
    s / (Real.sqrt ((q ^ a : ℕ) : ℝ) * Real.sqrt ((q ^ b : ℕ) : ℝ)) =
      (q : ℝ) ^ (-(((a + b : ℕ) : ℝ)) / 2) * s := by
  rw [← inverse_sqrt_pow_product]
  ring

end AES8.FiberNormalization
