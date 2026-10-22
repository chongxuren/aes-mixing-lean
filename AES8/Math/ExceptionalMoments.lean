/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.Imports
import AESMixing.Block

/-!
# Generic exceptional-block moment estimates

The sharp quadratic cap below is a finite real inequality.  Applied to
`t i = u i ^ 2`, it derives the exceptional fourth-moment constant `1250946`
from the explicit entry and energy hypotheses.  The inputs may be signed.

We use Cauchy--Schwarz for the cubic moment.  This gives `41004`, which is
weaker than the manuscript's `40017`; no proof of `40017` is claimed here.
The weaker bound still suffices for the same final scaled fourth-sum cap
`25 * 2 ^ 44`, using the zero sum and exactly `255` entries.

These are generic implications, not proofs that actual AES block entries
satisfy the hypotheses.  Their entry, energy, zero-sum, cardinality, and
translation-parameter instantiations remain separate obligations.
Constructive proof work only; no attacks or predecessor/manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.ExceptionalMoments

section FiniteCap
variable {I : Type*}

/-- Nonnegative cross terms bound the sum of squares by the square of the sum. -/
theorem sum_sq_le_sq_sum (s : Finset I) (t : I → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ t i) :
    (∑ i ∈ s, t i ^ 2) ≤ (∑ i ∈ s, t i) ^ 2 := by
  classical
  revert hnonneg
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert i s hi ih =>
      intro hnonneg
      have hi0 : 0 ≤ t i := hnonneg i (Finset.mem_insert_self _ _)
      have hs0 : ∀ j ∈ s, 0 ≤ t j :=
        fun j hj => hnonneg j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ s, t j :=
        Finset.sum_nonneg (fun j hj => hs0 j hj)
      have hrest := ih hs0
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      nlinarith [mul_nonneg hi0 hsum0]

/-- Sharp quadratic cap with room for one full entry and one remainder.
No bound on the number of entries is required. -/
theorem sharp_quadratic_cap (s : Finset I) (t : I → ℝ) (A B : ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ t i) (hcap : ∀ i ∈ s, t i ≤ A)
    (hsum : (∑ i ∈ s, t i) ≤ A + B) (hB0 : 0 ≤ B) (hBA : B ≤ A) :
    (∑ i ∈ s, t i ^ 2) ≤ A ^ 2 + B ^ 2 := by
  classical
  have hA0 : 0 ≤ A := hB0.trans hBA
  by_cases hsmall : ∀ i ∈ s, t i ≤ B
  · calc
      (∑ i ∈ s, t i ^ 2) ≤ ∑ i ∈ s, B * t i := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [mul_nonneg (hnonneg i hi) (sub_nonneg.mpr (hsmall i hi))]
      _ = B * ∑ i ∈ s, t i := (Finset.mul_sum _ _ _).symm
      _ ≤ B * (A + B) := mul_le_mul_of_nonneg_left hsum hB0
      _ ≤ A ^ 2 + B ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hBA) hA0]
  · have hex : ∃ j, j ∈ s ∧ B < t j := by
      by_contra hnone
      apply hsmall
      intro j hj
      by_contra hjB
      exact hnone ⟨j, hj, lt_of_not_ge hjB⟩
    obtain ⟨j, hj, hjB⟩ := hex
    have hrest0 : ∀ i ∈ s.erase j, 0 ≤ t i :=
      fun i hi => hnonneg i (Finset.mem_of_mem_erase hi)
    have hrestsum0 : 0 ≤ ∑ i ∈ s.erase j, t i :=
      Finset.sum_nonneg (fun i hi => hrest0 i hi)
    have hsplit : (∑ i ∈ s.erase j, t i) + t j = ∑ i ∈ s, t i :=
      Finset.sum_erase_add _ _ hj
    have hsplit2 : (∑ i ∈ s.erase j, t i ^ 2) + t j ^ 2 =
        ∑ i ∈ s, t i ^ 2 := Finset.sum_erase_add _ _ hj
    have hrestsum : (∑ i ∈ s.erase j, t i) ≤ A + B - t j := by
      linarith
    have hroom0 : 0 ≤ A + B - t j := hrestsum0.trans hrestsum
    have hrestsquare : (∑ i ∈ s.erase j, t i) ^ 2 ≤ (A + B - t j) ^ 2 :=
      (sq_le_sq₀ hrestsum0 hroom0).mpr hrestsum
    have hendpoints : t j ^ 2 + (A + B - t j) ^ 2 ≤ A ^ 2 + B ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hjB))
        (sub_nonneg.mpr (hcap j hj))]
    calc
      (∑ i ∈ s, t i ^ 2) = t j ^ 2 + ∑ i ∈ s.erase j, t i ^ 2 := by
        linarith
      _ ≤ t j ^ 2 + (∑ i ∈ s.erase j, t i) ^ 2 :=
        add_le_add le_rfl (sum_sq_le_sq_sum (s.erase j) t hrest0)
      _ ≤ t j ^ 2 + (A + B - t j) ^ 2 := add_le_add le_rfl hrestsquare
      _ ≤ A ^ 2 + B ^ 2 := hendpoints

end FiniteCap

section ExceptionalConstants
variable {I : Type*} [Fintype I]

/-- The manuscript's fourth-moment constant, derived from entry and energy caps. -/
theorem fourth_sum_le_1250946 (u : I → ℝ)
    (hentry : ∀ i, |u i| ≤ 33) (henergy : (∑ i : I, u i ^ 2) ≤ 1344) :
    (∑ i : I, u i ^ 4) ≤ 1250946 := by
  have hcap : ∀ i ∈ (Finset.univ : Finset I), u i ^ 2 ≤ (33 : ℝ) ^ 2 := by
    intro i _
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (u i)) (by norm_num : (0 : ℝ) ≤ 33)).mpr (hentry i)
  have hsum : (∑ i : I, u i ^ 2) ≤ (33 : ℝ) ^ 2 + 255 := by
    convert henergy using 1 <;> norm_num
  have h := sharp_quadratic_cap Finset.univ (fun i => u i ^ 2) ((33 : ℝ) ^ 2) 255
    (fun i _ => sq_nonneg (u i)) hcap hsum (by norm_num) (by norm_num)
  have hpower (i : I) : (u i ^ 2) ^ 2 = u i ^ 4 := by ring
  simp only [hpower] at h
  norm_num at h
  exact h

/-- A Cauchy--Schwarz cubic bound.  This deliberately does not claim `40017`. -/
theorem cubic_sum_lt_41004 (u : I → ℝ)
    (hentry : ∀ i, |u i| ≤ 33) (henergy : (∑ i : I, u i ^ 2) ≤ 1344) :
    (∑ i : I, |u i| ^ 3) < 41004 := by
  have hfourth := fourth_sum_le_1250946 u hentry henergy
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : I => |u i|) (fun i : I => u i ^ 2)
  have hterm (i : I) : |u i| * u i ^ 2 = |u i| ^ 3 := by
    rw [← sq_abs (u i)]
    ring
  have hpower (i : I) : (u i ^ 2) ^ 2 = u i ^ 4 := by ring
  simp only [hterm, sq_abs, hpower] at hcauchy
  have hfourth0 : 0 ≤ ∑ i : I, u i ^ 4 :=
    Finset.sum_nonneg (fun i _ => by
      rw [← hpower i]
      exact sq_nonneg _)
  have hprod : (∑ i : I, u i ^ 2) * (∑ i : I, u i ^ 4) ≤
      (1344 : ℝ) * 1250946 :=
    mul_le_mul henergy hfourth hfourth0 (by norm_num)
  have hcubic0 : 0 ≤ ∑ i : I, |u i| ^ 3 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (u i)) 3)
  have hsquare : (∑ i : I, |u i| ^ 3) ^ 2 < (41004 : ℝ) ^ 2 :=
    (hcauchy.trans hprod).trans_lt (by norm_num)
  by_contra hnot
  have hlower : (41004 : ℝ) ≤ ∑ i : I, |u i| ^ 3 := le_of_not_gt hnot
  have hsquare_lower :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 41004) hcubic0).mpr hlower
  linarith

end ExceptionalConstants

section Translation
variable {I : Type*} [Fintype I]

/-- Binomial expansion and a zero sum turn signed translation into moment bounds. -/
theorem translated_fourth_sum_le (u : I → ℝ) (c M2 M3 M4 : ℝ)
    (hc0 : 0 ≤ c) (hzero : (∑ i : I, u i) = 0)
    (hsecond : (∑ i : I, u i ^ 2) ≤ M2)
    (hthird : (∑ i : I, |u i| ^ 3) ≤ M3)
    (hfourth : (∑ i : I, u i ^ 4) ≤ M4) :
    (∑ i : I, (u i - c) ^ 4) ≤
      M4 + 4 * c * M3 + 6 * c ^ 2 * M2 + (Fintype.card I : ℝ) * c ^ 4 := by
  have hterm (i : I) : (u i - c) ^ 4 =
      u i ^ 4 - 4 * c * u i ^ 3 + 6 * c ^ 2 * u i ^ 2 -
        4 * c ^ 3 * u i + c ^ 4 := by ring
  have hexpand : (∑ i : I, (u i - c) ^ 4) =
      (∑ i : I, u i ^ 4) - 4 * c * (∑ i : I, u i ^ 3) +
        6 * c ^ 2 * (∑ i : I, u i ^ 2) + (Fintype.card I : ℝ) * c ^ 4 := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hzero, mul_zero, sub_zero]
  have hnegative : -(∑ i : I, u i ^ 3) ≤ ∑ i : I, |u i| ^ 3 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      -(u i ^ 3) ≤ |u i ^ 3| := neg_le_abs _
      _ = |u i| ^ 3 := abs_pow _ _
  have hcubic := mul_le_mul_of_nonneg_left (hnegative.trans hthird)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc0)
  have hquadratic := mul_le_mul_of_nonneg_left hsecond
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sq_nonneg c))
  rw [hexpand]
  nlinarith

/-- The looser cubic bound still gives a translated fourth sum below `1630000`.
Nonstrict parameter caps suffice, including both endpoints. -/
theorem translated_fourth_sum_lt_1630000 (u : I → ℝ) (c : ℝ)
    (hcard : Fintype.card I = 255) (hentry : ∀ i, |u i| ≤ 33)
    (henergy : (∑ i : I, u i ^ 2) ≤ 1344) (hzero : (∑ i : I, u i) = 0)
    (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ i : I, (u i - c) ^ 4) < 1630000 := by
  have hbound := translated_fourth_sum_le u c 1344 41004 1250946 hc0 hzero henergy
    (le_of_lt (cubic_sum_lt_41004 u hentry henergy))
    (fourth_sum_le_1250946 u hentry henergy)
  rw [hcard] at hbound
  have hc2 : c ^ 2 ≤ (33 / 16 : ℝ) ^ 2 :=
    (sq_le_sq₀ hc0 (by norm_num : (0 : ℝ) ≤ 33 / 16)).mpr hc
  have hc4 : c ^ 4 ≤ (33 / 16 : ℝ) ^ 4 := by
    have h := (sq_le_sq₀ (sq_nonneg c) (sq_nonneg (33 / 16 : ℝ))).mpr hc2
    nlinarith only [h]
  have hterm1 : 4 * c * 41004 ≤ (339000 : ℝ) := by nlinarith only [hc]
  have hterm2 : 6 * c ^ 2 * 1344 ≤ (35000 : ℝ) := by nlinarith only [hc2]
  have hterm4 : 255 * c ^ 4 ≤ (5000 : ℝ) := by nlinarith only [hc4]
  norm_num at hbound
  linarith

/-- The final exceptional-block fourth-sum cap, before actual AES instantiation. -/
theorem scaled_translated_fourth_sum_lt (u : I → ℝ) (c : ℝ)
    (hcard : Fintype.card I = 255) (hentry : ∀ i, |u i| ≤ 33)
    (henergy : (∑ i : I, u i ^ 2) ≤ 1344) (hzero : (∑ i : I, u i) = 0)
    (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ i : I, ((128 : ℝ) * (u i - c)) ^ 4) < 25 * 2 ^ 44 := by
  have htranslated := translated_fourth_sum_lt_1630000 u c hcard hentry henergy
    hzero hc0 hc
  calc
    (∑ i : I, ((128 : ℝ) * (u i - c)) ^ 4) =
        (128 : ℝ) ^ 4 * ∑ i : I, (u i - c) ^ 4 := by
      simp only [mul_pow, Finset.mul_sum]
    _ < (128 : ℝ) ^ 4 * 1630000 :=
      mul_lt_mul_of_pos_left htranslated (by norm_num)
    _ < 25 * 2 ^ 44 := by norm_num

end Translation

end AES8.ExceptionalMoments
