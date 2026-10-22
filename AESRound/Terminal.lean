import AESRound.Imports

/-!
# The terminal profile functional and rational round thresholds

The first four and last ten coordinates use exactly the embeddings used by the
finite certificates.  This file proves the analytic properties of the terminal
functional and the arithmetic consequences of the two eventual envelopes.

The connection from the AES experiment to these profile bounds is not asserted
here.  In particular, the tail estimates and monotonicity of the error sequence
remain explicit hypotheses in the numerical corollaries.
-/

noncomputable section

open scoped BigOperators

namespace AESRound.Terminal

/-- The fourteen nonnegative profile coordinates used by the terminal bound. -/
abbrev Profile := Fin 14 → ℝ

/-- Euclidean norm of a real profile on any finite index type. -/
def blockNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

theorem blockNorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ blockNorm x :=
  Real.sqrt_nonneg _

/-- Coordinatewise domination implies domination of norms for nonnegative data. -/
theorem blockNorm_mono {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    blockNorm x ≤ blockNorm y := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have hprod : 0 ≤ (y i - x i) * (y i + x i) :=
    mul_nonneg (sub_nonneg.mpr (hxy i)) (by linarith [hx i, hxy i])
  nlinarith [hprod]

/-- Positive homogeneity, with the sign condition on the scalar explicit. -/
theorem blockNorm_mul {ι : Type*} [Fintype ι] (α : ℝ) (x : ι → ℝ)
    (hα : 0 ≤ α) :
    blockNorm (fun i => α * x i) = α * blockNorm x := by
  have hsum : (∑ i, (α * x i) ^ 2) = α ^ 2 * ∑ i, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold blockNorm
  rw [hsum, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

/-- First-block Euclidean norm divided by `2^14`, plus the last-block norm. -/
def phi (x : Profile) : ℝ :=
  blockNorm (fun i : Fin 4 => x (Fin.castAdd 10 i)) / 16384 +
    blockNorm (fun i : Fin 10 => x (Fin.natAdd 4 i))

theorem phi_nonneg (x : Profile) : 0 ≤ phi x := by
  unfold phi
  exact add_nonneg
    (div_nonneg (blockNorm_nonneg _) (by norm_num))
    (blockNorm_nonneg _)

theorem phi_mono {x y : Profile} (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) : phi x ≤ phi y := by
  unfold phi
  exact add_le_add
    (div_le_div_of_nonneg_right
      (blockNorm_mono (fun i => hx (Fin.castAdd 10 i))
        (fun i => hxy (Fin.castAdd 10 i))) (by norm_num))
    (blockNorm_mono (fun i => hx (Fin.natAdd 4 i))
      (fun i => hxy (Fin.natAdd 4 i)))

theorem phi_monotoneOn_nonnegative :
    MonotoneOn phi {x : Profile | ∀ i, 0 ≤ x i} := by
  intro x hx y _ hxy
  exact phi_mono hx hxy

theorem phi_mul (α : ℝ) (x : Profile) (hα : 0 ≤ α) :
    phi (fun i => α * x i) = α * phi x := by
  change
    blockNorm (fun i : Fin 4 => α * x (Fin.castAdd 10 i)) / 16384 +
      blockNorm (fun i : Fin 10 => α * x (Fin.natAdd 4 i)) = α * phi x
  rw [blockNorm_mul α _ hα, blockNorm_mul α _ hα]
  unfold phi
  ring

theorem phi_smul (α : ℝ) (x : Profile) (hα : 0 ≤ α) :
    phi (α • x) = α * phi x := by
  change phi (fun i => α * x i) = α * phi x
  exact phi_mul α x hα

/-- Convert exact squared certificate witnesses into a terminal upper bound. -/
theorem phi_le_of_squared_bounds {x : Profile} {a r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hfirst : (∑ i : Fin 4, (x (Fin.castAdd 10 i)) ^ 2) ≤ a ^ 2)
    (hlast : (∑ i : Fin 10, (x (Fin.natAdd 4 i)) ^ 2) ≤ r ^ 2) :
    phi x ≤ a / 16384 + r := by
  have hfirstNorm : blockNorm (fun i : Fin 4 => x (Fin.castAdd 10 i)) ≤ a := by
    unfold blockNorm
    calc
      Real.sqrt (∑ i : Fin 4, (x (Fin.castAdd 10 i)) ^ 2) ≤ Real.sqrt (a ^ 2) :=
        Real.sqrt_le_sqrt hfirst
      _ = a := Real.sqrt_sq ha
  have hlastNorm : blockNorm (fun i : Fin 10 => x (Fin.natAdd 4 i)) ≤ r := by
    unfold blockNorm
    calc
      Real.sqrt (∑ i : Fin 10, (x (Fin.natAdd 4 i)) ^ 2) ≤ Real.sqrt (r ^ 2) :=
        Real.sqrt_le_sqrt hlast
      _ = r := Real.sqrt_sq hr
  exact add_le_add (div_le_div_of_nonneg_right hfirstNorm (by norm_num)) hlastNorm

/- The three threshold comparisons use rational arithmetic only.  They are
   consequences of upstream envelopes, not a formalization of those envelopes. -/

def lambda : ℝ := 101 / 2 ^ (48 : ℕ)

def c1 : ℝ := 33 / 5000

def c2 : ℝ := 1 / 250

theorem lambda_nonneg : 0 ≤ lambda := by
  norm_num [lambda]

theorem lambda_lt_one : lambda < 1 := by
  norm_num [lambda]

theorem c1_lambda_three_lt : c1 * lambda ^ 3 < (1 : ℝ) / 2 ^ (128 : ℕ) := by
  norm_num [c1, lambda]

theorem c2_lambda_five_lt : c2 * lambda ^ 5 < (1 : ℝ) / 2 ^ (192 : ℕ) := by
  norm_num [c2, lambda]

theorem c2_lambda_six_lt : c2 * lambda ^ 6 < (1 : ℝ) / 2 ^ (256 : ℕ) := by
  norm_num [c2, lambda]

/-- Ten rounds follow from the explicitly assumed `c1` envelope. -/
theorem ten_rounds_of_c1_tail (ε : ℕ → ℝ)
    (hC1 : ∀ m : ℕ, 2 ≤ m → ε (4 + 2 * m) < c1 * lambda ^ m) :
    ε 10 < (1 : ℝ) / 2 ^ (128 : ℕ) := by
  have h : ε 10 < c1 * lambda ^ 3 := by
    simpa using hC1 3 (by norm_num)
  exact h.trans c1_lambda_three_lt

/-- Fourteen rounds follow from the explicitly assumed `c2` envelope. -/
theorem fourteen_rounds_of_c2_tail (ε : ℕ → ℝ)
    (hC2 : ∀ m : ℕ, 4 ≤ m → ε (4 + 2 * m) < c2 * lambda ^ m) :
    ε 14 < (1 : ℝ) / 2 ^ (192 : ℕ) := by
  have h : ε 14 < c2 * lambda ^ 5 := by
    simpa using hC2 5 (by norm_num)
  exact h.trans c2_lambda_five_lt

/-- Sixteen rounds follow from the explicitly assumed `c2` envelope. -/
theorem sixteen_rounds_of_c2_tail (ε : ℕ → ℝ)
    (hC2 : ∀ m : ℕ, 4 ≤ m → ε (4 + 2 * m) < c2 * lambda ^ m) :
    ε 16 < (1 : ℝ) / 2 ^ (256 : ℕ) := by
  have h : ε 16 < c2 * lambda ^ 6 := by
    simpa using hC2 6 (by norm_num)
  exact h.trans c2_lambda_six_lt

/-- Extension beyond ten rounds additionally assumes antitonicity of `ε`. -/
theorem at_least_ten_rounds_of_c1_tail (ε : ℕ → ℝ)
    (hε : Antitone ε)
    (hC1 : ∀ m : ℕ, 2 ≤ m → ε (4 + 2 * m) < c1 * lambda ^ m)
    {r : ℕ} (hr : 10 ≤ r) :
    ε r < (1 : ℝ) / 2 ^ (128 : ℕ) :=
  (hε hr).trans_lt (ten_rounds_of_c1_tail ε hC1)

/-- Extension beyond fourteen rounds additionally assumes antitonicity of `ε`. -/
theorem at_least_fourteen_rounds_of_c2_tail (ε : ℕ → ℝ)
    (hε : Antitone ε)
    (hC2 : ∀ m : ℕ, 4 ≤ m → ε (4 + 2 * m) < c2 * lambda ^ m)
    {r : ℕ} (hr : 14 ≤ r) :
    ε r < (1 : ℝ) / 2 ^ (192 : ℕ) :=
  (hε hr).trans_lt (fourteen_rounds_of_c2_tail ε hC2)

/-- Extension beyond sixteen rounds additionally assumes antitonicity of `ε`. -/
theorem at_least_sixteen_rounds_of_c2_tail (ε : ℕ → ℝ)
    (hε : Antitone ε)
    (hC2 : ∀ m : ℕ, 4 ≤ m → ε (4 + 2 * m) < c2 * lambda ^ m)
    {r : ℕ} (hr : 16 ≤ r) :
    ε r < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  (hε hr).trans_lt (sixteen_rounds_of_c2_tail ε hC2)

theorem round_targets_of_tail_bounds (ε : ℕ → ℝ)
    (hC1 : ∀ m : ℕ, 2 ≤ m → ε (4 + 2 * m) < c1 * lambda ^ m)
    (hC2 : ∀ m : ℕ, 4 ≤ m → ε (4 + 2 * m) < c2 * lambda ^ m) :
    ε 10 < (1 : ℝ) / 2 ^ (128 : ℕ) ∧
      ε 14 < (1 : ℝ) / 2 ^ (192 : ℕ) ∧
      ε 16 < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  ⟨ten_rounds_of_c1_tail ε hC1,
    fourteen_rounds_of_c2_tail ε hC2,
    sixteen_rounds_of_c2_tail ε hC2⟩

end AESRound.Terminal
