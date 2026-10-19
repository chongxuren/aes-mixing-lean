import AESMixing.Gram
import AESMixing.ByteCollision
import AESMixing.KernelAlgebra
import Mathlib.Algebra.BigOperators.Fin

/-!
# Three-leg damped line responses

These identities keep all three output legs in the original joint tensor space.
A global absolute-cube bound for each pair kernel bounds the line response Gram;
no independence of a distribution and no Fourier/residual commutation is assumed.
Actual byte resource estimates and the line/plane shortening correspondence are
separate obligations. This module is constructive mathematics only.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.DampedLineGram
open AESMixing

variable {V X : Type*} [Fintype V] [Fintype X]

/-- Pointwise three-factor Holder, proved by an exact polynomial identity. -/
theorem three_mul_le_cubes (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * (a*b*c) ≤ a^3+b^3+c^3 := by
  have hp := mul_nonneg (show 0 ≤ a+b+c by positivity)
    (show 0 ≤ (a-b)^2+(b-c)^2+(c-a)^2 by positivity)
  nlinarith [hp]

theorem triple_sum_bound (u v w : X → ℝ) (C : ℝ)
    (hu : (∑ x, |u x|^3) ≤ C) (hv : (∑ x, |v x|^3) ≤ C)
    (hw : (∑ x, |w x|^3) ≤ C) :
    |∑ x, u x*v x*w x| ≤ C := by
  have hp (x : X) : 3*|u x*v x*w x| ≤ |u x|^3+|v x|^3+|w x|^3 := by
    simp only [abs_mul]
    exact three_mul_le_cubes _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hp x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht := Finset.abs_sum_le_sum_abs (fun x : X => u x*v x*w x) Finset.univ
  linarith

/-- A mixed Fourier entry cap and a squared-sum cap suffice for its cube sum. -/
theorem cube_sum_le_max_mul_square_sum (f : X → ℝ) (k t : ℝ)
    (hk : 0 ≤ k) (hmax : ∀ x, |f x| ≤ k) (hsecond : (∑ x, f x^2) ≤ t) :
    (∑ x, |f x|^3) ≤ k*t := by
  calc
    _ = ∑ x, |f x| * (f x)^2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_succ, sq_abs]
      ring
    _ ≤ ∑ x, k*(f x)^2 := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_right (hmax x) (sq_nonneg _))
    _ = k*∑ x, (f x)^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ k*t := mul_le_mul_of_nonneg_left hsecond hk

def crossGram (T U : V → V → ℝ) (a b : V) : ℝ :=
  ∑ y, T y a * U y b

theorem crossGram_self (T : V → V → ℝ) : crossGram T T = gram T := rfl

theorem crossGram_symmetry (T U : V → V → ℝ) (a b : V) :
    crossGram T U a b = crossGram U T b a := by
  unfold crossGram
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

/-- Composing the input of the right response keeps the actual cross Gram. -/
theorem crossGram_compose_right (T U F : V → V → ℝ) :
    crossGram T (kernelCompose U F) = kernelCompose (crossGram T U) F := by
  funext a b
  unfold crossGram kernelCompose
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem crossGram_compose_left (T U F : V → V → ℝ)
    (hF : ∀ a b, F a b = F b a) :
    crossGram (kernelCompose T F) U = kernelCompose F (crossGram T U) := by
  funext a b
  unfold crossGram kernelCompose
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  rw [hF z a]
  ring

/-- For a symmetric Fourier matrix the fourth pair kernel is F G F.
This identity does not assert that the residual itself commutes with F. -/
theorem crossGram_compose_both (T U F : V → V → ℝ)
    (hF : ∀ a b, F a b = F b a) :
    crossGram (kernelCompose T F) (kernelCompose U F) =
      kernelCompose F (kernelCompose (crossGram T U) F) := by
  rw [crossGram_compose_left _ _ _ hF, crossGram_compose_right]

def lineResponse (T : Fin 3 → V → V → ℝ) (e : Fin 3 → Equiv.Perm V)
    (y : Fin 3 → V) : ℝ :=
  (∑ x : V, ∏ i : Fin 3, T i (y i) (e i x)) / Fintype.card V

/-- The joint output energy is the product of the three actual pair kernels. -/
theorem lineResponse_inner (T U : Fin 3 → V → V → ℝ)
    (e f : Fin 3 → Equiv.Perm V) :
    (∑ y : Fin 3 → V, lineResponse T e y * lineResponse U f y) =
      (∑ x : V, ∑ z : V, ∏ i : Fin 3,
        crossGram (T i) (U i) (e i x) (f i z)) / (Fintype.card V : ℝ)^2 := by
  unfold lineResponse
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]
  congr 1
  · simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i y => T i y (e i x) * U i y (f i z))).symm
  · ring

theorem reindexed_cube_sum (G : V → V → ℝ) (e f : Equiv.Perm V) :
    (∑ p : V × V, |G (e p.1) (f p.2)|^3) =
      ∑ p : V × V, |G p.1 p.2|^3 := by
  exact Equiv.sum_comp (Equiv.prodCongr e f) (fun p : V × V => |G p.1 p.2|^3)

theorem lineResponse_inner_bound (T U : Fin 3 → V → V → ℝ)
    (e f : Fin 3 → Equiv.Perm V) (C : ℝ)
    (hC : ∀ i : Fin 3, (∑ p : V × V, |crossGram (T i) (U i) p.1 p.2|^3) ≤ C) :
    |∑ y : Fin 3 → V, lineResponse T e y * lineResponse U f y| ≤
      C / (Fintype.card V : ℝ)^2 := by
  have hr (i : Fin 3) :
      (∑ p : V × V, |crossGram (T i) (U i) (e i p.1) (f i p.2)|^3) ≤ C := by
    rw [reindexed_cube_sum]
    exact hC i
  have hb := triple_sum_bound
    (fun p : V × V => crossGram (T 0) (U 0) (e 0 p.1) (f 0 p.2))
    (fun p : V × V => crossGram (T 1) (U 1) (e 1 p.1) (f 1 p.2))
    (fun p : V × V => crossGram (T 2) (U 2) (e 2 p.1) (f 2 p.2))
    C (hr 0) (hr 1) (hr 2)
  rw [lineResponse_inner, abs_div,
    abs_of_nonneg (sq_nonneg (Fintype.card V : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa [Fin.prod_univ_succ, Fintype.sum_prod_type, mul_assoc] using hb

/-- In the AES normalization q=m^4, the source's line-Gram prefactor is m^2. -/
theorem byte_lineResponse_scaled_bound
    (T U : Fin 3 → BinaryWord 8 → BinaryWord 8 → ℝ)
    (e f : Fin 3 → Equiv.Perm (BinaryWord 8)) (C : ℝ)
    (hC : ∀ i : Fin 3,
      (∑ p : BinaryWord 8 × BinaryWord 8, |crossGram (T i) (U i) p.1 p.2|^3) ≤ C) :
    (4294967296 : ℝ) *
      |∑ y : Fin 3 → BinaryWord 8, lineResponse T e y * lineResponse U f y| ≤
      65536*C := by
  have h := lineResponse_inner_bound T U e f C hC
  norm_num [BinaryWord.card] at h
  linarith

end AESConcrete.DampedLineGram
