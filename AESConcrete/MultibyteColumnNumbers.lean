import AESConcrete.ActivityCollisionBox
import Mathlib.Tactic.IntervalCases

/-!
# Exact arithmetic for the proposed multibyte column aggregation

These are rational comparisons for the stated support and marked-coordinate
sums. They do not identify those sums with an actual word-column energy.
That requires the restricted response bounds, actual zero-event caps and
orthogonal support aggregation as separate proofs.

The constants and multiplicities follow the baseline appendix, equations
`byte-degree-energies` and `all-diagonals`. Constructive mathematics only;
no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MultibyteColumnNumbers

def rho : ℝ := 65 / 8192
def atom : ℝ := 1 / 64
def nu : ℝ := 9 / 128
def delta : ℝ := 8383 / 2088960
def q : ℝ := 2^32

def zeroCap (t z : ℕ) : ℝ :=
  if z = 1 then rho else
  if t = 3 ∧ z = 2 then atom * rho else
  if t = 4 ∧ z = 2 then rho^2 else
  if t = 4 ∧ z = 3 then atom^2 * rho else 0

def activityFactor (t : ℕ) : ℝ :=
  (1 - ∑ z ∈ Finset.range (t-1), (Nat.choose 4 (z+1) : ℝ) * zeroCap t (z+1))^2 +
    ∑ z ∈ Finset.range (t-1), (Nat.choose 4 (z+1) : ℝ) *
      255^(z+1) * zeroCap t (z+1)^2

def degreeCap (t j : ℕ) : ℝ :=
  ∑ z ∈ Finset.range t, if z+j ≤ 4 then
    (Nat.choose 4 z : ℝ) * (Nat.choose (4-z) j : ℝ) / 255^(4-z-j) *
      atom^(2*z) * (rho * nu^2)^(min (t-z) j) * delta^(j-min (t-z) j)
    else 0

def fullColumnCap (t : ℕ) : ℝ :=
  activityFactor t / 255^4 + ∑ j ∈ Finset.range 4, degreeCap t (j+1)

theorem zeroCap_endpoint (t z : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hz : 1 ≤ z ∧ z < t) :
    2 ≤ ((255 : ℝ)^z + 1) * zeroCap t z := by
  obtain ⟨ht0,ht1⟩ := ht
  obtain ⟨hz0,hz1⟩ := hz
  interval_cases t <;> interval_cases z <;> norm_num [zeroCap, rho, atom]

theorem activityFactor_two :
    activityFactor 2 = (1-4*rho)^2 + 4*255*rho^2 := by
  norm_num [activityFactor, zeroCap, Finset.sum_range_succ, Nat.choose]

theorem activityFactor_three :
    activityFactor 3 = (1-4*rho-6*atom*rho)^2 +
      4*255*rho^2 + 6*255^2*atom^2*rho^2 := by
  norm_num [activityFactor, zeroCap, Finset.sum_range_succ, Nat.choose]
  ring

theorem activityFactor_four :
    activityFactor 4 = (1-4*rho-6*rho^2-4*atom^2*rho)^2 +
      4*255*rho^2 + 6*255^2*rho^4 + 4*255^3*atom^4*rho^2 := by
  norm_num [activityFactor, zeroCap, Finset.sum_range_succ, Nat.choose]
  ring

theorem fullColumnCap_two : q * fullColumnCap 2 < 1078/1000 := by
  norm_num [q, fullColumnCap, activityFactor, degreeCap, zeroCap,
    rho, atom, nu, delta, Finset.sum_range_succ, Nat.choose]

theorem fullColumnCap_three : q * fullColumnCap 3 < 1072/1000 := by
  norm_num [q, fullColumnCap, activityFactor, degreeCap, zeroCap,
    rho, atom, nu, delta, Finset.sum_range_succ, Nat.choose]

theorem fullColumnCap_four : q * fullColumnCap 4 < 1069/1000 := by
  norm_num [q, fullColumnCap, activityFactor, degreeCap, zeroCap,
    rho, atom, nu, delta, Finset.sum_range_succ, Nat.choose]

theorem fullColumnCap_lt (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) :
    fullColumnCap t < 17/(15*q) := by
  have hq : 0 < q := by norm_num [q]
  have h : q * fullColumnCap t < 17/15 := by
    obtain ⟨ht0,ht1⟩ := ht
    interval_cases t
    · linarith [fullColumnCap_two]
    · linarith [fullColumnCap_three]
    · linarith [fullColumnCap_four]
  apply (lt_div_iff₀ (by positivity : 0 < 15*q)).mpr
  nlinarith

/-- Arithmetic centering, conditional on the separate full collision cap. -/
theorem centered_cap_lt (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (E : ℝ)
    (hE : E ≤ fullColumnCap t) : E - 1/(q-1) < 2/(15*q) := by
  have h := hE.trans_lt (fullColumnCap_lt t ht)
  have hc : 17/(15*q) - 1/(q-1) < 2/(15*q) := by norm_num [q]
  linarith

end AESConcrete.MultibyteColumnNumbers
