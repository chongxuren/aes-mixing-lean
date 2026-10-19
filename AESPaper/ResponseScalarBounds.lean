import AESPaper.WordRestrictedResponse

/-!
# Scalar conversion of whole-word restricted-response energies

The actual response estimates are supplied by the source/mask assembly. This
module only converts their scalar right-hand sides and takes nonnegative
square roots. In particular, `sqrt_bound_of_energy` keeps the response-energy
hypothesis explicit; it does not assert any source law or mask witness.
-/

set_option autoImplicit false
noncomputable section

namespace AESPaper.ResponseScalarBounds
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (delta)

theorem q_positive : 0 < q := by norm_num [q]

theorem q_ne_zero : q ≠ 0 := ne_of_gt q_positive

/-- Only the four-word cap is used to round the collision prefactor. -/
theorem collision_prefactor_le (a : ℕ) (ha4 : a ≤ 4) :
    (6 / 5 : ℝ)^a ≤ (6 / 5 : ℝ)^4 := by
  interval_cases a <;> norm_num

/-- The denominator in the displayed norm bound has exactly the required
squared power, including odd residual degree. -/
theorem squared_denominator (k j : ℕ) :
    (q^k * Real.sqrt (q^j))^2 = q^(2*k+j) := by
  have hpow : (q^k)^2 = q^(2*k) := by
    rw [← pow_mul, Nat.mul_comm k 2]
  rw [mul_pow, hpow, Real.sq_sqrt (pow_nonneg q_positive.le j), ← pow_add]

/-- Exact algebraic identity before applying any energy inequality. -/
theorem norm_coefficient_sq (k j a : ℕ) :
    ((6 / 5 : ℝ)^2 * 20^k * nu^a /
      (q^k * Real.sqrt (q^j)))^2 =
      (6 / 5 : ℝ)^4 * 20^(2*k) * nu^(2*a) / q^(2*k+j) := by
  have h20 : (20 : ℝ)^(2*k) = ((20 : ℝ)^k)^2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hnu : nu^(2*a) = (nu^a)^2 := by
    rw [Nat.mul_comm 2 a, pow_mul]
  rw [div_pow, squared_denominator, h20, hnu]
  ring

theorem norm_coefficient_nonnegative (k j a : ℕ) :
    0 ≤ (6 / 5 : ℝ)^2 * 20^k * nu^a /
      (q^k * Real.sqrt (q^j)) :=
  div_nonneg
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 20) k))
      (pow_nonneg WordDamping.nu_nonnegative a))
    (mul_nonneg (pow_nonneg q_positive.le k) (Real.sqrt_nonneg _))

/-- Scalar conversion shared by the low and high observation branches.
The imported actual word channel provides `0 ≤ delta < 1/q`; the conditions
here state precisely the two finite-index facts used by the conversion. -/
theorem squared_bound (k j a : ℕ) (haj : a ≤ j) (ha4 : a ≤ 4) :
    (20/q)^(2*k) * (6/(5*q))^a * nu^(2*a) * delta^(j-a) ≤
      (6 / 5 : ℝ)^4 * 20^(2*k) * nu^(2*a) / q^(2*k+j) := by
  have hdelta : delta^(j-a) ≤ (1/q)^(j-a) :=
    pow_le_pow_left₀ WordRestrictedResponse.delta_nonnegative
      WordRestrictedResponse.delta_lt_inv_q.le (j-a)
  have hleft : 0 ≤ (20/q)^(2*k) * (6/(5*q))^a * nu^(2*a) :=
    mul_nonneg
      (mul_nonneg
        (pow_nonneg (div_nonneg (by norm_num) q_positive.le) _)
        (pow_nonneg (div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) q_positive.le)) _))
      (pow_nonneg WordDamping.nu_nonnegative _)
  have hsplit : a + (j-a) = j := Nat.add_sub_of_le haj
  have hpowj : q^j = q^a * q^(j-a) := by
    calc
      q^j = q^(a+(j-a)) := congrArg (fun n : ℕ => q^n) hsplit.symm
      _ = q^a * q^(j-a) := pow_add _ _ _
  have hden : q^(2*k+j) = q^(2*k) * q^a * q^(j-a) := by
    calc
      q^(2*k+j) = q^(2*k) * q^j := pow_add _ _ _
      _ = q^(2*k) * q^a * q^(j-a) := by rw [hpowj]; ring
  calc
    _ ≤ (20/q)^(2*k) * (6/(5*q))^a * nu^(2*a) * (1/q)^(j-a) :=
      mul_le_mul_of_nonneg_left hdelta hleft
    _ = (6 / 5 : ℝ)^a * 20^(2*k) * nu^(2*a) / q^(2*k+j) := by
      rw [show (6 / (5*q) : ℝ) = ((6 : ℝ)/5)/q by rw [div_div], hden]
      simp only [div_pow, one_pow]
      field_simp [q_ne_zero]
      <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg q_positive.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (collision_prefactor_le a ha4)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _))
        (pow_nonneg WordDamping.nu_nonnegative _)

/-- A response-energy hypothesis is explicit and remains unnormalized.
The scalar result itself introduces no probabilistic or independence premise. -/
theorem sqrt_bound_of_energy (energy : ℝ) (k j a : ℕ)
    (haj : a ≤ j) (ha4 : a ≤ 4) (henergy_nonnegative : 0 ≤ energy)
    (henergy : energy ≤
      (20/q)^(2*k) * (6/(5*q))^a * nu^(2*a) * delta^(j-a)) :
    Real.sqrt energy ≤ (6 / 5 : ℝ)^2 * 20^k * nu^a /
      (q^k * Real.sqrt (q^j)) := by
  have hsq : energy ≤
      ((6 / 5 : ℝ)^2 * 20^k * nu^a /
        (q^k * Real.sqrt (q^j)))^2 :=
    (henergy.trans (squared_bound k j a haj ha4)).trans_eq
      (norm_coefficient_sq k j a).symm
  apply (sq_le_sq₀ (Real.sqrt_nonneg energy)
    (norm_coefficient_nonnegative k j a)).mp
  rw [Real.sq_sqrt henergy_nonnegative]
  exact hsq

end AESPaper.ResponseScalarBounds
