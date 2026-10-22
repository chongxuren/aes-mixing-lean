import AESRound.Recurrence
import AESRound.Terminal
import AESRound.CertificateChecks

/-!
# All-round consequence of the explicit profile interface

This is the finite-certificate/induction part of the source addendum.  The
interface is deliberately a parameter, not an axiom: it must still be proved
for the actual independently keyed AES experiment.  Neither the requested
round thresholds nor the eventual scalar envelopes are fields of the interface.
-/
noncomputable section
namespace AESRound
open Terminal

/-- Analytic interface for a single input/source.  `w` is its active-word class.
The starting profiles, recurrence, and terminal conversion are the outstanding
AES-specific obligations; all subsequent numerical and induction steps are
proved below. -/
structure ProfileInterface (ε : ℕ → ℝ) where
  w : Fin 4
  x : ℕ → AESRound.Profile (Fin 14)
  nonneg : ∀ n i, 0 ≤ x n i
  initial_zero : x 0 ≤ Certificate.y w 0
  initial_one : x 1 ≤ Certificate.y w 1
  recurrence : ∀ n, x (n + 2) ≤ comparisonStep Certificate.L Certificate.H
    Certificate.J (x (n + 1)) (x n)
  terminal : ∀ m, ε (4 + 2 * m) ≤ lambda ^ m / 2 ^ 17 * phi (x m)

namespace ProfileInterface
variable {ε : ℕ → ℝ} (M : ProfileInterface ε)

theorem prefix_bound : ∀ n, n ≤ 10 → M.x n ≤ Certificate.y M.w n := by
  apply finite_prefix_comparison Certificate.L_nonneg Certificate.H_nonneg
    Certificate.J_nonneg M.initial_zero M.initial_one M.recurrence
  intro n hn i
  simpa [comparisonStep, matVec, Certificate.mv] using
    Certificate.step M.w (n + 1) (by omega) (by omega) i

theorem early_cone : ∀ n, 6 ≤ n → M.x n ≤ fun i => 156000 * Certificate.d i := by
  apply invariant_cone_from_two_states Certificate.H_nonneg Certificate.J_nonneg
    (by norm_num : (0 : ℝ) ≤ 156000) M.recurrence
  · exact Certificate.cone
  · exact le_trans (M.prefix_bound 6 (by omega)) (Certificate.early_seed M.w 6 (Or.inl rfl))
  · exact le_trans (M.prefix_bound 7 (by omega)) (Certificate.early_seed M.w 7 (Or.inr rfl))

theorem late_cone : ∀ n, 9 ≤ n → M.x n ≤ fun i => 118000 * Certificate.d i := by
  apply invariant_cone_from_two_states Certificate.H_nonneg Certificate.J_nonneg
    (by norm_num : (0 : ℝ) ≤ 118000) M.recurrence
  · exact Certificate.cone
  · exact le_trans (M.prefix_bound 9 (by omega)) (Certificate.late_seed M.w 9 (Or.inl rfl))
  · exact le_trans (M.prefix_bound 10 (by omega)) (Certificate.late_seed M.w 10 (Or.inr rfl))

theorem finite_output (n : ℕ) (hn : n ≤ 10) :
    phi (M.x n) ≤ Certificate.aUpper M.w n / 16384 + Certificate.rUpper M.w n := by
  apply le_trans (phi_mono (M.nonneg n) (M.prefix_bound n hn))
  exact phi_le_of_squared_bounds (Certificate.aUpper_nonneg M.w n hn)
    (Certificate.rUpper_nonneg M.w n hn) (Certificate.aSquare_le M.w n hn)
    (Certificate.rSquare_le M.w n hn)

theorem cone_output : phi Certificate.d < (821 : ℝ) / 200000 := by
  exact lt_of_le_of_lt (phi_le_of_squared_bounds Certificate.dAUpper_nonneg
    Certificate.dRUpper_nonneg Certificate.dASquare_le Certificate.dRSquare_le)
    Certificate.d_output

theorem c1_profile (n : ℕ) (hn : 2 ≤ n) : phi (M.x n) < c1 * 2 ^ 17 := by
  by_cases hsmall : n ≤ 5
  · exact lt_of_le_of_lt (M.finite_output n (by omega)) (Certificate.finite_c1 M.w n hn hsmall)
  · have h := phi_mono (M.nonneg n) (M.early_cone n (by omega))
    rw [phi_mul _ _ (by norm_num)] at h
    have hd := cone_output
    have hc : (156000 : ℝ) * (821 / 200000) < c1 * 2 ^ 17 := by norm_num [c1]
    exact lt_of_le_of_lt h (lt_trans (mul_lt_mul_of_pos_left hd (by norm_num)) hc)

theorem c2_profile (n : ℕ) (hn : 4 ≤ n) : phi (M.x n) < c2 * 2 ^ 17 := by
  by_cases hsmall : n ≤ 8
  · exact lt_of_le_of_lt (M.finite_output n (by omega)) (Certificate.finite_c2 M.w n hn hsmall)
  · have h := phi_mono (M.nonneg n) (M.late_cone n (by omega))
    rw [phi_mul _ _ (by norm_num)] at h
    have hd := cone_output
    have hc : (118000 : ℝ) * (821 / 200000) < c2 * 2 ^ 17 := by norm_num [c2]
    exact lt_of_le_of_lt h (lt_trans (mul_lt_mul_of_pos_left hd (by norm_num)) hc)

include M

/-- The source's first eventual bound, for every even round index from m=2. -/
theorem c1_all_even (m : ℕ) (hm : 2 ≤ m) :
    ε (4 + 2 * m) < c1 * lambda ^ m := by
  have hpos : 0 < lambda ^ m / (2 : ℝ) ^ 17 := by
    have h_lambda : 0 < lambda := by norm_num [lambda]
    positivity
  calc
    ε (4 + 2 * m) ≤ lambda ^ m / 2 ^ 17 * phi (M.x m) := M.terminal m
    _ < lambda ^ m / 2 ^ 17 * (c1 * 2 ^ 17) :=
      mul_lt_mul_of_pos_left (M.c1_profile m hm) hpos
    _ = c1 * lambda ^ m := by ring

/-- The sharper bound from m=4, proved by finite prefix and a later cone. -/
theorem c2_all_even (m : ℕ) (hm : 4 ≤ m) :
    ε (4 + 2 * m) < c2 * lambda ^ m := by
  have hpos : 0 < lambda ^ m / (2 : ℝ) ^ 17 := by
    have h_lambda : 0 < lambda := by norm_num [lambda]
    positivity
  calc
    ε (4 + 2 * m) ≤ lambda ^ m / 2 ^ 17 * phi (M.x m) := M.terminal m
    _ < lambda ^ m / 2 ^ 17 * (c2 * 2 ^ 17) :=
      mul_lt_mul_of_pos_left (M.c2_profile m hm) hpos
    _ = c2 * lambda ^ m := by ring

/-- Larger round counts use the separate Markov-contraction obligation. -/
theorem c1_all_rounds (hε : Antitone ε) {m r : ℕ} (hm : 2 ≤ m)
    (hr : 4 + 2 * m ≤ r) : ε r < c1 * lambda ^ m :=
  lt_of_le_of_lt (hε hr) (M.c1_all_even m hm)

theorem c2_all_rounds (hε : Antitone ε) {m r : ℕ} (hm : 4 ≤ m)
    (hr : 4 + 2 * m ≤ r) : ε r < c2 * lambda ^ m :=
  lt_of_le_of_lt (hε hr) (M.c2_all_even m hm)

/-- The four-round cap is a separate inherited analytic premise. -/
def a0 : ℝ := (631 / 100) / 2 ^ 17

def c0 : ℝ := 167 / 1000

theorem c0_all_even (hfour : ε 4 < a0) (m : ℕ) :
    ε (4 + 2 * m) < c0 * lambda ^ m := by
  rcases m with _ | m
  · simpa using hfour.trans (by norm_num [a0, c0] : a0 < c0)
  rcases m with _ | m
  · have hp : 0 < lambda / (2 : ℝ) ^ 17 := by norm_num [lambda]
    have hprofile : phi (M.x 1) < c0 * 2 ^ 17 :=
      lt_of_le_of_lt (M.finite_output 1 (by omega)) (Certificate.finite_c0 M.w)
    calc
      ε (4 + 2 * (0 + 1)) ≤ lambda ^ 1 / 2 ^ 17 * phi (M.x 1) := M.terminal 1
      _ < lambda / 2 ^ 17 * (c0 * 2 ^ 17) := by
        simpa using mul_lt_mul_of_pos_left hprofile hp
      _ = c0 * lambda ^ (0 + 1) := by ring
  · have hpow : 0 < lambda ^ (m + 1 + 1) := by
      have h_lambda : 0 < lambda := by norm_num [lambda]
      positivity
    exact (M.c1_all_even (m + 1 + 1) (by omega)).trans
      (mul_lt_mul_of_pos_right (by norm_num [c1, c0]) hpow)

/-- Exact non-logarithmic form of the source's general all-round theorem.
It proves the numerical deduction from the profile, four-round, and
Markov-contraction interfaces, which remain visible parameters. -/
theorem all_rounds (hfour : ε 4 < a0) (hε : Antitone ε)
    {m r : ℕ} (hr : 4 + 2 * m ≤ r) :
    ε r < min a0 (c0 * lambda ^ m) := by
  apply lt_min
  · exact lt_of_le_of_lt (hε (by omega : 4 ≤ r)) hfour
  · exact lt_of_le_of_lt (hε hr) (M.c0_all_even hfour m)

/-- 10/14/16 are corollaries of the checked all-round profile theorem. -/
theorem round_targets :
    ε 10 < (1 : ℝ) / 2 ^ (128 : ℕ) ∧
    ε 14 < (1 : ℝ) / 2 ^ (192 : ℕ) ∧
    ε 16 < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  round_targets_of_tail_bounds ε M.c1_all_even M.c2_all_even

end ProfileInterface
end AESRound
