import AESPaper.UniformBias
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact pure J/Z tensor energy from a signed zero-event moment

Each one-word bias kernel has a two-valued rank-one factorization. A literal
J/Z tensor term therefore has one scalar moment against the possibly
correlated input, and its exact counting-measure energy is that moment squared
divided by `card^4 * (card-1)^|S|`. Full uniform includes the zero element.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.BiasTensorEnergy
open AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Q" => (Fintype.card V : ℝ)

/-- Joint probability mass at prescribed distinguished coordinates; no
normalization or independence is built into this definition. -/
def jointZeroMass (z : V) (g : (Fin 4 → V) → ℝ) (D : Finset (Fin 4)) : ℝ :=
  ∑ x, if (∀ i ∈ D, x i=z) then g x else 0

def basis (z x : V) : ℝ := if x=z then Q-1 else -1

def basisProduct (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, if i ∈ S then basis z (x i) else 1

def moment (z : V) (S : Finset (Fin 4)) (g : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ x, g x * basisProduct z S x

/-- Literal J/Z tensor kernel, with Z precisely at positions in S. -/
def kernel (z : V) (S : Finset (Fin 4)) (y x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, if i ∈ S then UniformBias.biasKernel z (y i) (x i)
    else UniformBias.uniformKernel (y i) (x i)

theorem constant_product (S : Finset (Fin 4)) (a b : ℝ) :
    (∏ i : Fin 4, a * (if i ∈ S then b else 1)) = a ^ 4 * b ^ S.card := by
  have hs : (Finset.univ.filter (fun i : Fin 4 => i ∈ S)) = S := by
    ext i
    simp
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hs, one_pow, mul_one]

/-- The factorization uses a scalar denominator and introduces no square root. -/
theorem biasKernel_eq (z : V) (hn : 1 < Fintype.card V) (y x : V) :
    UniformBias.biasKernel z y x = basis z y * basis z x / (Q * (Q-1)) := by
  have hQ : (1 : ℝ) < Q := by exact_mod_cast hn
  have h0 : Q ≠ 0 := by linarith
  have h1 : Q-1 ≠ 0 := by linarith
  by_cases hy : y=z <;> by_cases hx : x=z
  all_goals simp [UniformBias.biasKernel, UniformBias.uniformKernel, activityMatrix,
    basis, hy, hx]
  all_goals field_simp [h0, h1] <;> ring

theorem basis_square_sum (z : V) : (∑ y, basis z y ^ 2) = Q * (Q-1) := by
  have hp (y : V) : basis z y ^ 2 =
      1 + if y=z then (Q-1)^2-1 else 0 := by
    by_cases hy : y=z <;> simp [basis, hy] <;> ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem basisProduct_square_sum (z : V) (S : Finset (Fin 4)) :
    (∑ y : Fin 4 → V, basisProduct z S y ^ 2) = Q ^ 4 * (Q-1) ^ S.card := by
  have hp (y : Fin 4 → V) : basisProduct z S y ^ 2 =
      ∏ i : Fin 4, if i ∈ S then basis z (y i) ^ 2 else 1 := by
    unfold basisProduct
    rw [pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi, pow_two]
  have hc (i : Fin 4) :
      (∑ y : V, if i ∈ S then basis z y ^ 2 else 1) =
        Q * (if i ∈ S then Q-1 else 1) := by
    by_cases hi : i ∈ S <;>
      simp [hi, basis_square_sum, Finset.card_univ, nsmul_eq_mul]
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun i (y : V) => if i ∈ S then basis z y ^ 2 else 1)]
  simp_rw [hc]
  exact constant_product S Q (Q-1)

theorem kernel_eq (z : V) (hn : 1 < Fintype.card V) (S : Finset (Fin 4))
    (y x : Fin 4 → V) :
    kernel z S y x = basisProduct z S y * basisProduct z S x /
      (Q ^ 4 * (Q-1) ^ S.card) := by
  have hp (i : Fin 4) :
      (if i ∈ S then UniformBias.biasKernel z (y i) (x i)
        else UniformBias.uniformKernel (y i) (x i)) =
      ((if i ∈ S then basis z (y i) else 1) *
        (if i ∈ S then basis z (x i) else 1)) /
          (Q * (if i ∈ S then Q-1 else 1)) := by
    by_cases hi : i ∈ S
    · simpa only [if_pos hi] using biasKernel_eq z hn (y i) (x i)
    · simp [hi, UniformBias.uniformKernel]
  unfold kernel
  simp_rw [hp]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, constant_product]
  rfl

theorem action_eq (z : V) (hn : 1 < Fintype.card V) (S : Finset (Fin 4))
    (g : (Fin 4 → V) → ℝ) (y : Fin 4 → V) :
    action (kernel z S) g y =
      (basisProduct z S y / (Q ^ 4 * (Q-1) ^ S.card)) * moment z S g := by
  have hp (x : Fin 4 → V) : kernel z S y x * g x =
      (basisProduct z S y / (Q ^ 4 * (Q-1) ^ S.card)) *
        (g x * basisProduct z S x) := by
    rw [kernel_eq z hn S]
    ring
  unfold action
  simp_rw [hp]
  rw [← Finset.mul_sum]
  rfl

/-- Exact pure-bias energy. The moment retains the full joint source law. -/
theorem energy_eq (z : V) (hn : 1 < Fintype.card V) (S : Finset (Fin 4))
    (g : (Fin 4 → V) → ℝ) :
    (∑ y, action (kernel z S) g y ^ 2) =
      moment z S g ^ 2 / (Q ^ 4 * (Q-1) ^ S.card) := by
  have hQ : (1 : ℝ) < Q := by exact_mod_cast hn
  have h0 : Q ≠ 0 := by linarith
  have h1 : Q-1 ≠ 0 := by linarith
  have hp (y : Fin 4 → V) :
      ((basisProduct z S y / (Q ^ 4 * (Q-1) ^ S.card)) * moment z S g) ^ 2 =
      basisProduct z S y ^ 2 *
        (moment z S g ^ 2 / (Q ^ 4 * (Q-1) ^ S.card) ^ 2) := by ring
  calc
    _ = (∑ y : Fin 4 → V, basisProduct z S y ^ 2) *
        (moment z S g ^ 2 / (Q ^ 4 * (Q-1) ^ S.card) ^ 2) := by
      simp only [action_eq z hn S, hp, Finset.sum_mul]
    _ = _ := by
      rw [basisProduct_square_sum]
      field_simp [h0, h1] <;> ring

end AESPaper.BiasTensorEnergy
