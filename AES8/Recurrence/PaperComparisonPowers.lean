import AES8.Math.HalfPowerMonomial
import AES8.Recurrence.PaperComparisonGraphs

/-!
# Real-power formulas behind the rational graph certificates

Frozen paper f902bb94, equations step-closed-form and aesasm-whole-graph.
These are scalar identities, separate from operator estimates and certificate
inequalities. Signed exponents use integers; natural subtractions are justified
by the displayed dimension hypotheses. No physical AES estimate is assumed.
-/
noncomputable section
namespace AES8.PaperComparisonPowers
open AES8.HalfPowerMonomial AES8.PaperComparison

set_option autoImplicit false

private theorem sqrtQ_pos : (0 : ℝ) < (sqrtQ : ℝ) := by
  norm_num [sqrtQ]
private theorem E_nonneg : (0 : ℝ) ≤ (E : ℝ) := by norm_num [E]
private theorem H_nonneg : (0 : ℝ) ≤ (H : ℝ) := by norm_num [H]

/-- Shared exact conversion used by the graph formulas, without dimensions. -/
theorem certificate_monomial (a b c : ℚ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (r e h : ℕ) (z : ℤ) :
    ((a : ℝ) / (sqrtQ : ℝ)) ^ r *
      Real.rpow ((b : ℝ) ^ 2 / (q : ℝ)) ((e : ℝ) / 2) *
      Real.rpow ((c : ℝ) ^ 2 / (q : ℝ)) ((h : ℝ) / 2) *
      Real.rpow (q : ℝ) ((z : ℝ) / 2) =
    ((a ^ r * b ^ e * c ^ h * qp (z - r - e - h) : ℚ) : ℝ) := by
  have hq : (q : ℝ) = (sqrtQ : ℝ) ^ (2 : ℕ) := by norm_num [q, sqrtQ]
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  rw [hq, ← div_pow, ← div_pow]
  rw [half_power_monomial _ _ _ _ sqrtQ_pos hb' hc']
  simp only [qp, Rat.cast_mul, Rat.cast_pow, Rat.cast_zpow]

/-- Literal real formula for the scaled fixed-position step. -/
def stepCoefficient (i j s : ℕ) : ℝ :=
  let r := min i s
  let z := min s (min i j)
  Real.rpow (q : ℝ) (((i : ℝ) + j - 2 - z) / 2) *
    ((C : ℝ) / (sqrtQ : ℝ)) ^ r *
    Real.rpow ((E : ℝ) ^ 2 / (q : ℝ)) (((i : ℝ) - r) / 2)

theorem stepCoefficient_eq (i j s : ℕ) :
    stepCoefficient i j s =
      ((C ^ min i s * E ^ (i - min i s) *
        qp ((j : ℤ) - 2 - min s (min i j)) : ℚ) : ℝ) := by
  let r := min i s
  let z := min s (min i j)
  have hr : r ≤ i := Nat.min_le_left _ _
  have he : ((i - r : ℕ) : ℝ) = (i : ℝ) - r := Nat.cast_sub hr
  have hz : (((i : ℤ) + j - 2 - z : ℤ) : ℝ) = (i : ℝ) + j - 2 - z := by
    push_cast
    rfl
  have h := certificate_monomial C E 1 (by norm_num [E]) (by norm_num)
    r (i-r) 0 ((i : ℤ) + j - 2 - z)
  simp only [Nat.cast_zero, zero_div, Real.rpow_eq_pow, Real.rpow_zero, mul_one, pow_zero] at h
  rw [he, hz] at h
  have hex : (i : ℤ) + j - 2 - z - r - (i-r : ℕ) - 0 = (j : ℤ) - 2 - z := by
    rw [Int.ofNat_sub hr]
    ring
  rw [hex] at h
  unfold stepCoefficient
  dsimp only
  simpa only [Real.rpow_eq_pow, r, z, mul_comm, mul_left_comm, mul_assoc] using h

/-- Includes the paper's zero branch when strict shortening fails. -/
def paperStepGraph (i a j b : ℕ) : ℝ :=
  let n := i+j
  let d := a+b+n-4
  if survives n d then stepCoefficient i j (min d (n-d)) else 0

theorem stepGraph_eq (i a j b : ℕ) :
    (stepGraph i a j b : ℝ) = paperStepGraph i a j b := by
  simp only [stepGraph, paperStepGraph]
  split_ifs <;> simp only [Rat.cast_zero, stepCoefficient_eq]

/-- The Q^3-scaled whole-graph formula, with tau=300/Q. -/
def wholeCoefficient (i j c s z : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (((i : ℝ) + j + 2*c - 2 - s - z)/2) *
    (300/(q : ℝ))^s *
    Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)+c-2*s)/2)

theorem wholeGraph_eq (i j c s z : ℕ) (hfit : 2*s ≤ i+c) :
    (wholeGraph i j c s z : ℝ) = wholeCoefficient i j c s z := by
  have hq : (q : ℝ) = (sqrtQ : ℝ) ^ (2 : ℕ) := by norm_num [q, sqrtQ]
  have he : ((i+c-2*s : ℕ) : ℝ) = (i : ℝ)+c-2*s := by
    rw [Nat.cast_sub hfit]
    push_cast
    rfl
  have hz : (((i : ℤ)+j+2*c-2-s-z : ℤ) : ℝ) =
      (i : ℝ)+j+2*c-2-s-z := by push_cast; rfl
  have h := normalized_weighted_powers (300 : ℝ) (E : ℝ) 1 (sqrtQ : ℝ)
    sqrtQ_pos.ne' 2 1 0 s (i+c-2*s) 0 ((i : ℤ)+j+2*c-2-s-z)
  simp only [mul_zero, Nat.cast_zero, sub_zero, pow_zero, mul_one] at h
  have hex : (i : ℤ)+j+2*c-2-s-z-(2*s : ℕ)-(1*(i+c-2*s) : ℕ) =
      (j : ℤ)+c-2-s-z := by
    rw [Nat.one_mul, Int.ofNat_sub hfit]
    push_cast
    ring
  rw [hex] at h
  unfold wholeGraph wholeCoefficient
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, qp, Rat.cast_zpow]
  rw [hq, ← div_pow, ← he, ← hz, square_half_nat _ _ (div_nonneg E_nonneg sqrtQ_pos.le),
    square_half_int _ _ sqrtQ_pos.le]
  simpa only [pow_one, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Scaled incidence times large overlap after collecting equal resource bases.
The paper uses the two low-fiber counts m,n; the min choices are applied below. -/
def largeCoefficient (i j c s t r z m n : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-r-z)/2) *
    ((C : ℝ)/(sqrtQ : ℝ))^(r+s+t-c) *
    Real.rpow ((E : ℝ)^2/(q : ℝ))
      (((i : ℝ)-r+2*c-s-t-m-n)/2) *
    Real.rpow ((H : ℝ)^2/(q : ℝ)^2) (((m : ℝ)+n)/2)

theorem largeCoefficient_eq (i j c s t r z m n : ℕ)
    (hr : r ≤ i) (hc : c ≤ s+t) (hs : s ≤ c) (ht : t ≤ c)
    (hm : m ≤ c-s) (hn : n ≤ c-t) :
    largeCoefficient i j c s t r z m n =
      ((C^(r+s+t-c) * E^(i-r+2*c-s-t-m-n) * H^(m+n) *
        qp ((j : ℤ)+c-2-r-z-m-n) : ℚ) : ℝ) := by
  let e := i-r+2*c-s-t-m-n
  have hfit : s+t+m+n ≤ 2*c := by omega
  have he : (e : ℝ) = (i : ℝ)-r+2*c-s-t-m-n := by
    have heq : e = (i-r)+(2*c-(s+t+m+n)) := by dsimp [e]; omega
    rw [heq, Nat.cast_add, Nat.cast_sub hr, Nat.cast_sub hfit]
    push_cast
    ring
  have hz : (((i : ℤ)+j+2*c-2-r-z : ℤ) : ℝ) =
      (i : ℝ)+j+2*c-2-r-z := by push_cast; rfl
  have hq : (q : ℝ) = (sqrtQ : ℝ)^2 := by norm_num [q, sqrtQ]
  have h := normalized_weighted_powers (C : ℝ) (E : ℝ) (H : ℝ) (sqrtQ : ℝ)
    sqrtQ_pos.ne' 1 1 2 (r+s+t-c) e (m+n) ((i : ℤ)+j+2*c-2-r-z)
  have heZ : (e : ℤ) = (i : ℤ)-r+2*c-s-t-m-n := by exact_mod_cast he
  have hrfit : c ≤ r+s+t := by omega
  have hex : (i : ℤ)+j+2*c-2-r-z-(1*(r+s+t-c) : ℕ)-
      (1*e : ℕ)-(2*(m+n) : ℕ) = (j : ℤ)+c-2-r-z-m-n := by
    simp only [Nat.one_mul, Int.ofNat_sub hrfit, Int.natCast_add,
      Int.natCast_mul, heZ]
    ring
  rw [hex] at h
  unfold largeCoefficient
  rw [hq, ← div_pow, ← div_pow, ← he, ← hz]
  have hmn : ((m : ℝ)+n)/2 = ((m+n : ℕ) : ℝ)/2 := by push_cast; rfl
  rw [hmn, square_half_nat _ _ (div_nonneg E_nonneg sqrtQ_pos.le),
    square_half_nat _ _ (div_nonneg H_nonneg (sq_nonneg _)),
    square_half_int _ _ sqrtQ_pos.le]
  simp only [qp, Rat.cast_mul, Rat.cast_pow, Rat.cast_zpow]
  simpa only [e, pow_one, mul_comm, mul_left_comm, mul_assoc] using h

theorem overlapLarge_eq (i j c s t r z af bf : ℕ)
    (hr : r ≤ i) (hc : c ≤ s+t) (hs : s ≤ c) (ht : t ≤ c) :
    (overlapLarge i j c s t r z af bf : ℝ) =
      largeCoefficient i j c s t r z (min (c-s) af) (min (c-t) bf) := by
  exact (largeCoefficient_eq i j c s t r z _ _ hr hc hs ht
    (Nat.min_le_left _ _) (Nat.min_le_left _ _)).symm

/-- Scaled incidence times the equal-Fourier Hilbert--Schmidt expression. -/
def hsCoefficient (i j c s t r z : ℕ) : ℝ :=
  let hi := max s t
  let lo := min s t
  Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-r-z)/2) *
    ((C : ℝ)/(sqrtQ : ℝ))^r *
    Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-r+hi-lo)/2) *
    Real.rpow ((H : ℝ)^2/(q : ℝ)) ((lo : ℝ)/2) *
    (27/(q : ℝ))^(c-hi)

theorem overlapHS_eq (i j c s t r z : ℕ)
    (hr : r ≤ i) (hs : s ≤ c) (ht : t ≤ c) :
    (overlapHS i j c s t r z : ℝ) = hsCoefficient i j c s t r z := by
  let hi := max s t
  let lo := min s t
  have hhi : hi ≤ c := max_le hs ht
  have hlo : lo ≤ hi := le_trans (Nat.min_le_left s t) (Nat.le_max_left s t)
  have hfit : lo ≤ i-r+hi := by omega
  have he : ((i-r+hi-lo : ℕ) : ℝ) = (i : ℝ)-r+hi-lo := by
    rw [Nat.cast_sub hfit, Nat.cast_add, Nat.cast_sub hr]
  have hz : (((i : ℤ)+j+2*c-2-r-z : ℤ) : ℝ) =
      (i : ℝ)+j+2*c-2-r-z := by push_cast; rfl
  have hq : (q : ℝ) = (sqrtQ : ℝ)^2 := by norm_num [q, sqrtQ]
  have h := normalized_four_powers (C : ℝ) (E : ℝ) (H : ℝ) 27 (sqrtQ : ℝ)
    sqrtQ_pos.ne' 1 1 1 2 r (i-r+hi-lo) lo (c-hi) ((i : ℤ)+j+2*c-2-r-z)
  have hex : (i : ℤ)+j+2*c-2-r-z-(1*r : ℕ)-
      (1*(i-r+hi-lo) : ℕ)-(1*lo : ℕ)-(2*(c-hi) : ℕ) =
      (j : ℤ)+hi-2-r-z := by
    simp only [Nat.one_mul, Int.ofNat_sub hfit, Int.ofNat_sub hr,
      Int.ofNat_sub hhi, Int.natCast_add, Int.natCast_mul]
    ring
  rw [hex] at h
  unfold overlapHS hsCoefficient
  dsimp only
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, qp, Rat.cast_zpow]
  rw [hq, ← div_pow, ← div_pow, ← he, ← hz,
    square_half_nat _ _ (div_nonneg E_nonneg sqrtQ_pos.le),
    square_half_nat _ _ (div_nonneg H_nonneg sqrtQ_pos.le),
    square_half_int _ _ sqrtQ_pos.le]
  simpa only [hi, lo, pow_one, mul_comm, mul_left_comm, mul_assoc] using h.symm

end AES8.PaperComparisonPowers
