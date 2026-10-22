/- Module role: Frozen numerical-profile route; not the current paper theorem.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.Certificate
import AES8.Historical.Output

/-!
# The profile recurrence and its dyadic output bound

This module proves a conditional numerical theorem.  `ProfileBounds` is the
explicit interface that an AES application must establish; no concrete AES
law, key model, or security experiment is identified with that interface here.
The finite prefix and invariant use the exact rational certificates, while
the output estimate uses the square-root functional in `AES8.Output`.
Constructive correctness verification only; no attack development.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace AES8

/-- The two-round geometric factor, written with a natural-number exponent. -/
def omega41 : ℝ := 1 / 2 ^ (41 : ℕ)

/-- The obligations left to the concrete application of the profile theorem. -/
structure ProfileBounds (epsilon : ℕ → ℝ) (z : ℕ → Profile) : Prop where
  nonnegative : ∀ j i, 0 ≤ z j i
  initial : z 0 ≤ scale 1000 u0
  first : z 1 ≤ fun i => L (z 0) i + 1000 * g i
  step : ∀ j, z (j + 2) ≤ fun i => L (z (j + 1)) i + M (z j) i
  output : ∀ j,
    epsilon (4 + 2 * j) ≤ (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ j * Phi (z j)

/-- Positivity of the scalar permits a scaled, monotone recurrence step. -/
theorem scaled_update_le {a : ℝ} (ha : 0 ≤ a)
    {x y u v w : Profile} (hx : x ≤ scale a u) (hy : y ≤ scale a v)
    (hw : (fun i => L u i + M v i) ≤ w) :
    (fun i => L x i + M y i) ≤ scale a w := by
  have hL := L_mono hx
  have hM := M_mono hy
  rw [L_scale] at hL
  rw [M_scale] at hM
  intro i
  calc
    L x i + M y i ≤ scale a (L u) i + scale a (M v) i :=
      add_le_add (hL i) (hM i)
    _ = a * (L u i + M v i) := by simp only [scale]; ring
    _ ≤ scale a w i := mul_le_mul_of_nonneg_left (hw i) ha

theorem profile_bound_1 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 1 ≤ scale 1000 u1 := by
  have hL := L_mono hb.initial
  rw [L_scale] at hL
  intro i
  calc
    z 1 i ≤ L (z 0) i + 1000 * g i := hb.first i
    _ ≤ scale 1000 (L u0) i + 1000 * g i :=
      add_le_add (hL i) le_rfl
    _ = 1000 * (L u0 i + g i) := by simp only [scale]; ring
    _ ≤ scale 1000 u1 i :=
      mul_le_mul_of_nonneg_left (prefix01 i) (by norm_num)

theorem profile_bound_2 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 2 ≤ scale 1000 u2 := by
  exact (hb.step 0).trans
    (scaled_update_le (by norm_num) (profile_bound_1 hb) hb.initial prefix12)

theorem profile_bound_3_prefix {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 3 ≤ scale 1000 u3 := by
  exact (hb.step 1).trans
    (scaled_update_le (by norm_num) (profile_bound_2 hb) (profile_bound_1 hb) prefix23)

theorem profile_bound_4_prefix {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 4 ≤ scale 1000 u4 := by
  exact (hb.step 2).trans
    (scaled_update_le (by norm_num) (profile_bound_3_prefix hb) (profile_bound_2 hb)
      prefix34)

theorem profile_bound_3 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 3 ≤ scale 10000 h := by
  apply (profile_bound_3_prefix hb).trans
  intro i
  have hi := u3_box i
  change u3 i ≤ 10 * h i at hi
  change 1000 * u3 i ≤ 10000 * h i
  linarith

theorem profile_bound_4 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : z 4 ≤ scale 10000 h := by
  apply (profile_bound_4_prefix hb).trans
  intro i
  have hi := u4_box i
  change u4 i ≤ 10 * h i at hi
  change 1000 * u4 i ≤ 10000 * h i
  linarith

/-- A two-term induction keeps both predecessors inside the same invariant box. -/
theorem profile_tail_pair {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) (j : ℕ) :
    z (j + 3) ≤ scale 10000 h ∧ z (j + 4) ≤ scale 10000 h := by
  induction j with
  | zero => exact ⟨profile_bound_3 hb, profile_bound_4 hb⟩
  | succ j ih =>
      have hn : z ((j + 3) + 2) ≤ scale 10000 h :=
        (hb.step (j + 3)).trans
          (scaled_update_le (by norm_num)
            (by simpa [Nat.add_assoc] using ih.2) ih.1 invariant)
      constructor
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.2
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn

theorem profile_tail {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) (j : ℕ) : z (j + 3) ≤ scale 10000 h :=
  (profile_tail_pair hb j).1

theorem profile_bound_of_three_le {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) {j : ℕ} (hj : 3 ≤ j) :
    z j ≤ scale 10000 h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa [Nat.add_comm] using profile_tail hb k

theorem output_profile_2_lt_32 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : Phi (z 2) < 32 :=
  lt_of_le_of_lt (Phi_mono (hb.nonnegative 2) (profile_bound_2 hb)) Phi_1000_u2_lt

/-- The prefix is sharper than needed; the common threshold makes all k uniform. -/
theorem output_profile_lt_128 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) (k : ℕ) : Phi (z (k + 2)) < 128 := by
  cases k with
  | zero =>
      exact lt_trans (output_profile_2_lt_32 hb) (by norm_num)
  | succ k =>
      apply lt_of_le_of_lt _ Phi_10000_h_lt
      apply Phi_mono (hb.nonnegative (k + 1 + 2))
      intro i
      simpa [Nat.add_assoc] using profile_tail hb k i

theorem omega41_pos : 0 < omega41 := by norm_num [omega41]

/-- Exact dyadic arithmetic, isolated from the profile and output arguments. -/
theorem output_constant (k : ℕ) :
    (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) * 128 =
      (1 / 2 ^ (92 : ℕ) : ℝ) * omega41 ^ k := by
  have hc : (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ 2 * 128 =
      (1 / 2 ^ (92 : ℕ) : ℝ) := by norm_num [omega41]
  calc
    _ = ((1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ 2 * 128) * omega41 ^ k := by
      rw [pow_add]
      ring
    _ = _ := by rw [hc]

theorem dyadic_target (k : ℕ) :
    (1 / 2 ^ (92 : ℕ) : ℝ) * omega41 ^ k =
      (1 : ℝ) / 2 ^ (92 + 41 * k) := by
  simp only [omega41, pow_add, pow_mul, one_div, inv_pow, mul_inv_rev]
  ring

/-- Conditional profile theorem: the concrete AES-to-profile bridge is separate. -/
theorem eight_plus_two {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) (k : ℕ) :
    epsilon (8 + 2 * k) < (1 : ℝ) / 2 ^ (92 + 41 * k) := by
  have hout := hb.output (k + 2)
  have hround : 4 + 2 * (k + 2) = 8 + 2 * k := by omega
  rw [hround] at hout
  have hfactor : 0 < (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) :=
    mul_pos (by positivity) (pow_pos omega41_pos _)
  calc
    epsilon (8 + 2 * k) ≤
        (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) * Phi (z (k + 2)) := hout
    _ < (1 / 2 ^ (17 : ℕ) : ℝ) * omega41 ^ (k + 2) * 128 :=
      mul_lt_mul_of_pos_left (output_profile_lt_128 hb k) hfactor
    _ = (1 / 2 ^ (92 : ℕ) : ℝ) * omega41 ^ k := output_constant k
    _ = (1 : ℝ) / 2 ^ (92 + 41 * k) := dyadic_target k

theorem ten_round_exact {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : epsilon 10 < (1 : ℝ) / 2 ^ (133 : ℕ) := by
  simpa using eight_plus_two hb 1

theorem ten_round_128 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : epsilon 10 < (1 : ℝ) / 2 ^ (128 : ℕ) :=
  lt_trans (ten_round_exact hb) (by norm_num)

theorem fourteen_round_exact {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : epsilon 14 < (1 : ℝ) / 2 ^ (215 : ℕ) := by
  simpa using eight_plus_two hb 3

theorem fourteen_round_192 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : epsilon 14 < (1 : ℝ) / 2 ^ (192 : ℕ) :=
  lt_trans (fourteen_round_exact hb) (by norm_num)

theorem sixteen_round_256 {epsilon : ℕ → ℝ} {z : ℕ → Profile}
    (hb : ProfileBounds epsilon z) : epsilon 16 < (1 : ℝ) / 2 ^ (256 : ℕ) := by
  simpa using eight_plus_two hb 4

end AES8
