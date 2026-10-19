import AESMixing.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

/-! Exact reference-law correction used in the four-round smoothing proof. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def uniformExcept (zero : ι) (x : ι) : ℝ :=
  if x = zero then 0 else 1 / (Fintype.card ι - 1 : ℝ)

theorem centered_energy (p : ι → ℝ) (zero : ι)
    (hn : 1 < Fintype.card ι) (hz : p zero = 0) (hs : ∑ x, p x = 1) :
    energy p (uniformExcept zero) = (∑ x, p x ^ 2) -
      1 / (Fintype.card ι - 1 : ℝ) := by
  have hn' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hd : (Fintype.card ι - 1 : ℝ) ≠ 0 := by linarith
  have hprod (x : ι) : p x * uniformExcept zero x =
      p x / (Fintype.card ι - 1 : ℝ) := by
    by_cases hx : x = zero
    · subst x; simp [hz, uniformExcept]
    · simp [uniformExcept, hx, div_eq_mul_inv]
  have hsquare : (∑ x, uniformExcept zero x ^ 2) =
      1 / (Fintype.card ι - 1 : ℝ) := by
    have hpoint (x : ι) : uniformExcept zero x ^ 2 =
        (1 / (Fintype.card ι - 1 : ℝ)) ^ 2 -
          if x = zero then (1 / (Fintype.card ι - 1 : ℝ)) ^ 2 else 0 := by
      by_cases hx : x = zero <;> simp [uniformExcept, hx]
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  unfold energy
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsquare]
  have hc : (∑ x, 2 * p x * uniformExcept zero x) =
      2 / (Fintype.card ι - 1 : ℝ) := by
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum, ← Finset.sum_div, hs]
    ring
  rw [hc]
  ring

end AESMixing
