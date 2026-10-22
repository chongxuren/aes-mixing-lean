import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.Linarith

/-! Evaluation preserves low-degree polynomial and rational identities below
an element's algebraic degree. The degree-six case is the symbolic slope
specialization step; the concrete slope table is a separate obligation. -/
noncomputable section
namespace AES8.PaperAlgebraicSpecialization
open Polynomial
set_option autoImplicit false
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem eval_ne_zero (a : F) (p : K[X]) (hp : p ≠ 0)
    (hdeg : p.natDegree < (minpoly K a).natDegree) : aeval a p ≠ 0 := by
  intro h
  have hd := Polynomial.natDegree_le_of_dvd (minpoly.dvd K a h) hp
  exact (not_lt_of_ge hd) hdeg

theorem eval_eq_iff (a : F) (d : ℕ) (ha : d < (minpoly K a).natDegree)
    (p q : K[X]) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    aeval a p = aeval a q ↔ p = q := by
  constructor
  · intro h
    by_contra hn
    have hd : (p-q).natDegree < (minpoly K a).natDegree :=
      lt_of_le_of_lt (le_trans (natDegree_sub_le p q) (max_le hp hq)) ha
    exact eval_ne_zero a (p-q) (sub_ne_zero.mpr hn) hd (by simp [h])
  · rintro rfl
    rfl

theorem cubic_ratio_eq_iff (a : F) (ha : 6 < (minpoly K a).natDegree)
    (p q r s : K[X]) (hp : p.natDegree ≤ 3) (hq : q.natDegree ≤ 3)
    (hr : r.natDegree ≤ 3) (hs : s.natDegree ≤ 3) (hq0 : q ≠ 0) (hs0 : s ≠ 0) :
    aeval a p / aeval a q = aeval a r / aeval a s ↔ p*s=r*q := by
  have hq' : aeval a q ≠ 0 := eval_ne_zero a q hq0 (by omega)
  have hs' : aeval a s ≠ 0 := eval_ne_zero a s hs0 (by omega)
  rw [div_eq_div_iff hq' hs']
  rw [← map_mul, ← map_mul]
  apply eval_eq_iff a 6 ha
  · exact le_trans natDegree_mul_le (by omega)
  · exact le_trans natDegree_mul_le (by omega)

theorem cubic_ratio_ne (a : F) (ha : 6 < (minpoly K a).natDegree)
    (p q r s : K[X]) (hp : p.natDegree ≤ 3) (hq : q.natDegree ≤ 3)
    (hr : r.natDegree ≤ 3) (hs : s.natDegree ≤ 3) (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hne : p*s ≠ r*q) : aeval a p / aeval a q ≠ aeval a r / aeval a s :=
  mt (cubic_ratio_eq_iff a ha p q r s hp hq hr hs hq0 hs0).mp hne

end AES8.PaperAlgebraicSpecialization
