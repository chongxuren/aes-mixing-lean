/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.FiniteTensorEnergy
import AESMixing.L2Sums

/-!
# Encoding arbitrary coefficients through an information set

The information coordinates identify the source point exactly. Retain those
coordinates as labels while applying the other local maps; their column
energies multiply. The final tensor action on the labels uses the existing
finite-coordinate energy theorem. Inputs may be signed and correlated.

This is the generic encoding lemma of the manuscript. The equivalence and
local bounds are explicit; actual MDS and AES instantiations remain separate.
Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.InformationEncoding
open AESMixing

variable {C V I J : Type*} [Fintype C] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

def kernel (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → V → V → ℝ) (B : J → V → V → ℝ)
    (y : (I → V) × (J → V)) (c : C) : ℝ :=
  (∏ i, A i (y.1 i) (e c i)) * (∏ j, B j (y.2 j) (rest c j))

theorem remaining_energy (B : J → V → V → ℝ) (delta : ℝ)
    (hB : ∀ j x, (∑ y, B j y x ^ 2) ≤ delta) (x : J → V) :
    (∑ y : J → V, (∏ j, B j (y j) (x j)) ^ 2) ≤ delta ^ Fintype.card J := by
  calc
    _ = ∏ j : J, ∑ y : V, B j y (x j) ^ 2 := by
      simp_rw [← Finset.prod_pow]
      exact (Fintype.prod_sum (fun j y => B j y (x j) ^ 2)).symm
    _ ≤ ∏ _ : J, delta := Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun y _ => sq_nonneg _)) (fun j _ => hB j _)
    _ = delta ^ Fintype.card J := by simp

theorem action_factor (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → V → V → ℝ) (B : J → V → V → ℝ) (f : C → ℝ)
    (y : I → V) (z : J → V) :
    action (kernel e rest A B) f (y,z) =
      action (coordinateKernel A)
        (fun x => f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) y := by
  unfold action kernel coordinateKernel
  rw [← e.symm.sum_comp (fun c =>
    ((∏ i, A i (y i) (e c i)) * ∏ j, B j (z j) (rest c j)) * f c)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [e.apply_symm_apply]
  ring

/-- Squared operator bound, retaining a different local map in each position. -/
theorem encoding_energy (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → V → V → ℝ) (B : J → V → V → ℝ) (nu : I → ℝ) (delta : ℝ)
    (hA : ∀ i g, (∑ y, action (A i) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hB : ∀ j x, (∑ y, B j y x ^ 2) ≤ delta) (f : C → ℝ) :
    (∑ y, action (kernel e rest A B) f y ^ 2) ≤
      (∏ i, nu i) ^ 2 * delta ^ Fintype.card J * ∑ c, f c ^ 2 := by
  have hrest : (∑ x : I → V, ∑ z : J → V,
      (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2) ≤
      delta ^ Fintype.card J * ∑ c, f c ^ 2 := by
    calc
      _ = ∑ x : I → V, f (e.symm x) ^ 2 *
          ∑ z : J → V, (∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 := by
        simp_rw [mul_pow, ← Finset.mul_sum]
      _ ≤ ∑ x : I → V, f (e.symm x) ^ 2 * delta ^ Fintype.card J :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          (remaining_energy B delta hB (rest (e.symm x))) (sq_nonneg _))
      _ = delta ^ Fintype.card J * ∑ c, f c ^ 2 := by
        rw [← Finset.sum_mul, e.symm.sum_comp (fun c => f c ^ 2)]
        ring
  simp only [Fintype.sum_prod_type, action_factor]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z : J → V, (∏ i, nu i) ^ 2 * ∑ x : I → V,
        (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 :=
      Finset.sum_le_sum (fun z _ =>
        AESConcrete.FiniteTensorEnergy.coordinate_energy A nu hA _)
    _ = (∏ i, nu i) ^ 2 * ∑ x : I → V, ∑ z : J → V,
        (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hrest (sq_nonneg (∏ i, nu i))
      simpa only [mul_assoc] using hb

/-- The corresponding counting-norm bound, with no sign assumption on `f`. -/
theorem encoding_l2 (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → V → V → ℝ) (B : J → V → V → ℝ) (nu : I → ℝ) (delta : ℝ)
    (hnu : ∀ i, 0 ≤ nu i) (hd : 0 ≤ delta)
    (hA : ∀ i g, (∑ y, action (A i) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hB : ∀ j x, (∑ y, B j y x ^ 2) ≤ delta) (f : C → ℝ) :
    l2 (action (kernel e rest A B) f) ≤
      ((∏ i, nu i) * Real.sqrt delta ^ Fintype.card J) * l2 f := by
  have hs : (Real.sqrt delta ^ Fintype.card J) ^ 2 = delta ^ Fintype.card J := by
    rw [← pow_mul, Nat.mul_comm (Fintype.card J) 2, pow_mul, Real.sq_sqrt hd]
  apply l2_le_of_energy _ f _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hnu i))
      (pow_nonneg (Real.sqrt_nonneg _) _))
  simpa only [mul_pow, hs, mul_assoc] using encoding_energy e rest A B nu delta hA hB f

end AES8.InformationEncoding
