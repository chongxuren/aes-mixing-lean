import AESPaper.Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
Five-component postprocessing from v9 Appendix D. All analytic inputs are
explicit hypotheses. z is the normalized weighted profile
  z_k = 2^80 D⁻¹ x(f_{4+4k}), D = diag(4096,5,1,3/20,1/80).
The code does not identify an arbitrary sequence z with concrete AES.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AESPaper

abbrev Profile := Fin 5 → ℝ
noncomputable def weights : Profile := ![4096, 5, 1, 3 / 20, 1 / 80]
noncomputable def initialProfile : Profile := ![21 / 10, 63 / 10, 1 / 4, 7 / 100, 1 / 80]
noncomputable def initialEnvelope : Profile := ![1 / 1000, 63 / 50, 1 / 4, 1 / 2, 1]
noncomputable def comparisonMatrix : Fin 5 → Fin 5 → ℝ :=
  ![![1730, 3, 4, 3, 19],
    ![228, 236, 434, 420, 59],
    ![2, 8, 448, 477, 510],
    ![1, 2, 79, 460, 1129],
    ![1, 1, 5, 20, 1744]]

noncomputable def step (z : Profile) (i : Fin 5) : ℝ :=
  (∑ j, comparisonMatrix i j * z j) / (1000000 * 2 ^ 64)

noncomputable def score (z : Profile) : ℝ :=
  z 0 / 4 + Real.sqrt ((5 * z 1) ^ 2 + (z 2) ^ 2 +
    ((3 / 20) * z 3) ^ 2 + ((1 / 80) * z 4) ^ 2)

theorem matrix_nonneg (i j : Fin 5) : 0 ≤ comparisonMatrix i j := by
  fin_cases i <;> fin_cases j <;> norm_num [comparisonMatrix]

theorem initial_envelope_valid (i : Fin 5) :
    initialProfile i / weights i ≤ initialEnvelope i := by
  fin_cases i <;> norm_num [initialProfile, weights, initialEnvelope]

theorem matrix_rows (i : Fin 5) : ∑ j, comparisonMatrix i j ≤ 1771 := by
  fin_cases i <;> norm_num [comparisonMatrix, Fin.sum_univ_succ]

theorem row_rounding : (1771 : ℕ) * 560 < 1000000 := by norm_num

theorem step_mono {a b : Profile} (h : ∀ i, a i ≤ b i) (i : Fin 5) :
    step a i ≤ step b i := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (matrix_nonneg i j)

theorem initial_step (i : Fin 5) : step initialEnvelope i < blockRate := by
  fin_cases i <;> norm_num [step, initialEnvelope, comparisonMatrix, Fin.sum_univ_succ, blockRate]

theorem constant_step (b : ℝ) (hb : 0 ≤ b) (i : Fin 5) :
    step (fun _ => b) i ≤ blockRate * b := by
  fin_cases i <;>
    norm_num [step, comparisonMatrix, Fin.sum_univ_succ, blockRate] <;> nlinarith

theorem score_mono {a b : Profile} (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    score a ≤ score b := by
  have h1 : (5 * a 1) ^ 2 ≤ (5 * b 1) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (ha 1))
    linarith [hab 1]
  have h2 : (a 2) ^ 2 ≤ (b 2) ^ 2 := pow_le_pow_left₀ (ha 2) (hab 2) 2
  have h3 : ((3 / 20 : ℝ) * a 3) ^ 2 ≤ ((3 / 20 : ℝ) * b 3) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (ha 3))
    linarith [hab 3]
  have h4 : ((1 / 80 : ℝ) * a 4) ^ 2 ≤ ((1 / 80 : ℝ) * b 4) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (ha 4))
    linarith [hab 4]
  unfold score
  apply add_le_add (by linarith [hab 0])
  apply Real.sqrt_le_sqrt
  linarith

theorem score_initial : score initialEnvelope < (32 / 5 : ℝ) := by
  have h : Real.sqrt ((63 / 10 : ℝ)^2 + (1 / 4)^2 + (3 / 40)^2 + (1 / 80)^2) < 631 / 100 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
  change (1/1000 : ℝ)/4 + Real.sqrt ((5*(63/50))^2 + (1/4)^2 +
    ((3/20)*(1/2))^2 + ((1/80)*1)^2) < 32/5
  norm_num at h ⊢
  linarith

theorem score_constant (b : ℝ) (hb : 0 < b) : score (fun _ => b) < (27 / 5) * b := by
  have h : Real.sqrt ((5*b)^2 + b^2 + ((3/20)*b)^2 + ((1/80)*b)^2) < (103/20)*b := by
    apply (Real.sqrt_lt' (by positivity)).2
    nlinarith [sq_pos_of_pos hb]
  unfold score
  linarith

/-- The first full matrix multiplication improves the initial weighted envelope. -/
theorem profile_iterations (z : ℕ → Profile)
    (hinit : ∀ i, z 0 i ≤ initialEnvelope i)
    (hstep : ∀ k i, z (k + 1) i ≤ step (z k) i) :
    ∀ k i, z (k + 1) i ≤ blockRate ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa using (hstep 0 i).trans ((step_mono hinit i).trans (initial_step i).le)
  | succ k ih =>
      intro i
      calc
        z (k + 1 + 1) i ≤ step (z (k + 1)) i := hstep (k+1) i
        _ ≤ step (fun _ => blockRate ^ (k + 1)) i := step_mono ih i
        _ ≤ blockRate * blockRate ^ (k + 1) :=
          constant_step _ (pow_nonneg blockRate_pos.le _) i
        _ = blockRate ^ (k + 1 + 1) := by rw [pow_succ]; ring

/-- Conditional analytic-to-numeric interface, not a theorem about concrete AES. -/
theorem mixing_bound_of_profiles (epsilon : ℕ → ℝ) (z : ℕ → Profile)
    (hz : ∀ k i, 0 ≤ z k i)
    (hinit : ∀ i, z 0 i ≤ initialEnvelope i)
    (hstep : ∀ k i, z (k + 1) i ≤ step (z k) i)
    (htv : ∀ k, epsilon (4 + 4*k) ≤ (1 / 2^17 : ℝ) * score (z k))
    (hmono : Antitone epsilon) (k r : ℕ) (hr : 4 + 4*k ≤ r) :
    epsilon r < rationalBound k ∧ rationalBound k < decimalBound k := by
  refine ⟨lt_of_le_of_lt (hmono hr) ?_, rational_lt_decimal k⟩
  cases k with
  | zero =>
      have hs : score (z 0) < (32 / 5 : ℝ) :=
        lt_of_le_of_lt (score_mono (hz 0) hinit) score_initial
      have ht := (htv 0).trans_lt (mul_lt_mul_of_pos_left hs (by norm_num : (0:ℝ) < 1/2^17))
      norm_num [rationalBound, initialCoefficient] at ht ⊢
      exact ht
  | succ k =>
      have hs : score (z (k+1)) < (27 / 5) * blockRate ^ (k+1) :=
        lt_of_le_of_lt (score_mono (hz _) (profile_iterations z hinit hstep k))
          (score_constant _ (pow_pos blockRate_pos _))
      have ht := (htv (k+1)).trans_lt
        (mul_lt_mul_of_pos_left hs (by norm_num : (0:ℝ) < 1/2^17))
      have hp := pow_pos blockRate_pos (k+1)
      unfold rationalBound initialCoefficient
      norm_num only [Nat.succ_eq_add_one] at *
      nlinarith

end AESPaper
