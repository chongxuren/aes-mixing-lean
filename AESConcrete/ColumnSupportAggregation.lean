import AESConcrete.MultibyteColumnNumbers
import AESMixing.SupportDegreeDecomposition

/-!
# Orthogonal support accounting for the multibyte column

This module only assembles separately proved component estimates. It retains
the exact multiplicities from the established support-index cardinality
theorem and the exact degree decomposition. Actual component and activity
estimates must be supplied by the AES specialization.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ColumnSupportAggregation
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.MultibyteColumnNumbers
open AESConcrete.WordColumnGram (Byte Word)

def supportCap (t z j : ℕ) : ℝ :=
  if z < t then
    1 / 255^(4-(z+j)) * atom^(2*z) *
      (rho*nu^2)^(min (t-z) j) * delta^(j-min (t-z) j)
  else 0

theorem support_cap_sum (t : ℕ) (j : Fin 5) :
    (∑ p : SupportIndex j.val, supportCap t (maskSize p.val.2) j.val) =
      ∑ a : Fin (5-j.val), (Nat.choose 4 j.val * Nat.choose (4-j.val) a.val : ℕ) *
        supportCap t (4-j.val-a.val) j.val := by
  have he (p : SupportIndex j.val) : maskSize p.val.2 = 4-j.val-(supportIndexSize p).val := by
    have h := supportIndexSize_eq p
    have hz := AESMixing.maskSize_le_four p.val.2
    omega
  simp_rw [he]
  exact supportIndex_sum_by_size j (fun a => supportCap t (4-j.val-a.val) j.val)

/-- The same binomial support sum as the numerical coefficient table. -/
theorem support_cap_sum_eq_degree (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (j : Fin 5) (hj : 1 ≤ j.val) :
    (∑ p : SupportIndex j.val, supportCap t (maskSize p.val.2) j.val) = degreeCap t j.val := by
  rw [support_cap_sum]
  obtain ⟨ht0,ht1⟩ := ht
  fin_cases j
  · norm_num at hj
  · change (∑ a : Fin 4, (4 * Nat.choose 3 a.val : ℕ) * supportCap t (3-a.val) 1) = degreeCap t 1
    rw [Fin.sum_univ_four]
    interval_cases t <;> norm_num [supportCap, degreeCap, atom, rho, nu, delta,
      Finset.sum_range_succ, Nat.choose]
  · change (∑ a : Fin 3, (6 * Nat.choose 2 a.val : ℕ) * supportCap t (2-a.val) 2) = degreeCap t 2
    rw [Fin.sum_univ_three]
    interval_cases t <;> norm_num [supportCap, degreeCap, atom, rho, nu, delta,
      Finset.sum_range_succ, Nat.choose]
  · change (∑ a : Fin 2, (4 * Nat.choose 1 a.val : ℕ) * supportCap t (1-a.val) 3) = degreeCap t 3
    rw [Fin.sum_univ_two]
    interval_cases t <;> norm_num [supportCap, degreeCap, atom, rho, nu, delta,
      Finset.sum_range_succ, Nat.choose]
  · change (∑ a : Fin 1, (1 * Nat.choose 0 a.val : ℕ) * supportCap t (0-a.val) 4) = degreeCap t 4
    simp only [Fin.sum_univ_one]
    interval_cases t <;> norm_num [supportCap, degreeCap, atom, rho, nu, delta,
      Finset.sum_range_succ, Nat.choose]

theorem positive_degree_energy_le (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (j : Fin 5) (hj : 1 ≤ j.val) (f : Word → ℝ)
    (hcomponent : ∀ p : SupportIndex j.val,
      (∑ y : Word, supportIndexComponent (0 : Byte) p f y^2) ≤
        supportCap t (maskSize p.val.2) j.val) :
    (∑ y : Word, degreeComponent (0 : Byte) j f y^2) ≤ degreeCap t j.val := by
  rw [supportIndex_degree_energy 0 (by norm_num [Byte, BinaryWord.card]) j f]
  calc
    _ ≤ ∑ p : SupportIndex j.val, supportCap t (maskSize p.val.2) j.val :=
      Finset.sum_le_sum (fun p _ => hcomponent p)
    _ = _ := support_cap_sum_eq_degree t ht j hj

/-- The five degrees are orthogonal. The degree-zero estimate retains the
support-probability normalization through its separate activityFactor. -/
theorem full_energy_le (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (f : Word → ℝ)
    (hactivity : (∑ y : Word, degreeComponent (0 : Byte) 0 f y^2) ≤ activityFactor t / 255^4)
    (hcomponent : ∀ (j : Fin 5), 1 ≤ j.val → ∀ p : SupportIndex j.val,
      (∑ y : Word, supportIndexComponent (0 : Byte) p f y^2) ≤
        supportCap t (maskSize p.val.2) j.val) :
    (∑ y : Word, f y^2) ≤ fullColumnCap t := by
  rw [← degreeComponent_pythagoras (0 : Byte) (by norm_num [Byte, BinaryWord.card]) f]
  rw [Fin.sum_univ_succ]
  calc
    _ ≤ activityFactor t / 255^4 + ∑ j : Fin 4, degreeCap t j.succ.val := by
      apply add_le_add hactivity
      apply Finset.sum_le_sum
      intro j _
      exact positive_degree_energy_le t ht j.succ (by simp) f (hcomponent j.succ (by simp))
    _ = _ := by
      unfold fullColumnCap
      congr 1

end AESConcrete.ColumnSupportAggregation
