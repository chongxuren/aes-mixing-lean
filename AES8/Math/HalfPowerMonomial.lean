import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! Reusable algebra for half powers and integer-power certificate monomials.
The equalities require the displayed positive base and preserve signed exponents.
No cryptographic constants or bounds belong in this module. -/
noncomputable section
namespace AES8.HalfPowerMonomial

theorem square_half_power (x z : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ (2 : ℕ)) (z / 2) = Real.rpow x z := by
  change (x ^ (2 : ℕ)) ^ (z / 2 : ℝ) = x ^ z
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

theorem square_half_nat (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    Real.rpow (x ^ (2 : ℕ)) ((n : ℝ) / 2) = x ^ n := by
  rw [square_half_power x n hx]
  exact Real.rpow_natCast x n

theorem square_half_int (x : ℝ) (z : ℤ) (hx : 0 ≤ x) :
    Real.rpow (x ^ (2 : ℕ)) ((z : ℝ) / 2) = x ^ z := by
  rw [square_half_power x z hx]
  exact Real.rpow_intCast x z

/-- All denominator powers collect into one signed integer exponent. -/
theorem normalized_powers (a b c x : ℝ) (hx : x ≠ 0)
    (r e h : ℕ) (z : ℤ) :
    (a / x) ^ r * (b / x) ^ e * (c / x) ^ h * x ^ z =
      a ^ r * b ^ e * c ^ h * x ^ (z - (r : ℤ) - (e : ℤ) - (h : ℤ)) := by
  rw [zpow_sub₀ hx, zpow_sub₀ hx, zpow_sub₀ hx]
  simp only [zpow_natCast, div_pow]
  ring

/-- The same collection when resources contain different denominator powers. -/
theorem normalized_weighted_powers (a b c x : ℝ) (hx : x ≠ 0)
    (u v w r e h : ℕ) (z : ℤ) :
    (a / x^u)^r * (b / x^v)^e * (c / x^w)^h * x^z =
      a^r * b^e * c^h * x^(z - (u*r : ℕ) - (v*e : ℕ) - (w*h : ℕ)) := by
  rw [zpow_sub₀ hx, zpow_sub₀ hx, zpow_sub₀ hx]
  simp only [zpow_natCast, div_pow, pow_mul]
  ring

/-- Four local resource powers with independently scaled denominators. -/
theorem normalized_four_powers (a b c d x : ℝ) (hx : x ≠ 0)
    (u v w k r e h f : ℕ) (z : ℤ) :
    (a/x^u)^r * (b/x^v)^e * (c/x^w)^h * (d/x^k)^f * x^z =
      a^r * b^e * c^h * d^f *
        x^(z-(u*r : ℕ)-(v*e : ℕ)-(w*h : ℕ)-(k*f : ℕ)) := by
  rw [zpow_sub₀ hx, zpow_sub₀ hx, zpow_sub₀ hx, zpow_sub₀ hx]
  simp only [zpow_natCast, div_pow, pow_mul]
  ring

/-- Convert squared resource parameters and an alphabet half power together. -/
theorem half_power_monomial (a b c x : ℝ) (hx : 0 < x)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (r e h : ℕ) (z : ℤ) :
    (a / x) ^ r * Real.rpow ((b / x) ^ (2 : ℕ)) ((e : ℝ) / 2) *
      Real.rpow ((c / x) ^ (2 : ℕ)) ((h : ℝ) / 2) *
      Real.rpow (x ^ (2 : ℕ)) ((z : ℝ) / 2) =
        a ^ r * b ^ e * c ^ h * x ^ (z - (r : ℤ) - (e : ℤ) - (h : ℤ)) := by
  rw [square_half_nat _ _ (div_nonneg hb hx.le),
    square_half_nat _ _ (div_nonneg hc hx.le), square_half_int _ _ hx.le]
  exact normalized_powers a b c x hx.ne' r e h z
end AES8.HalfPowerMonomial
