/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.InformationEncoding

/-!
# Two-code information overlap on arbitrary signed input

The output information coordinates are `A + B`, while the input information
coordinates are `B + E`. The other coordinates may depend on the full
corresponding information label. The action factors exactly into creation
of the `A` labels, tensor transport on `B`, and contraction of the `E` labels.
Column energies control creation and row energies control contraction.

All finite types, including empty coordinate types, are generic. No sign,
product-law, injectivity, or fiber-constancy condition is imposed on the
input or on the two coordinate maps. Actual marked MDS codes, incidence
normalizations, the shared word activity metric, local AES resources, and
the physical return cap are separate integration obligations.

Constructive proof work only; no attacks or manuscript/predecessor changes.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace AES8.InformationOverlap
open AESMixing

variable {A B E V : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype V]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- Literal overlap kernel in the two information-coordinate systems. -/
def kernel
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ)
    (y : (A → V) × (B → V))
    (x : (B → V) × (E → V)) : ℝ :=
  (∏ a, KA a (y.1 a) (leftCode x a)) *
  (∏ b, KB b (y.2 b) (x.1 b)) *
  (∏ e, KE e (rightCode y e) (x.2 e))

/-- Create the output-only labels while retaining the full input label. -/
def leftStage
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ)
    (f : ((B → V) × (E → V)) → ℝ)
    (a : A → V) (b : B → V) (e : E → V) : ℝ :=
  (∏ i, KA i (a i) (leftCode (b,e) i)) * f (b,e)

/-- Apply the shared-coordinate tensor, keeping both other labels. -/
def middleStage (KB : B → V → V → ℝ)
    (g : (A → V) → (B → V) → (E → V) → ℝ)
    (a : A → V) (b : B → V) (e : E → V) : ℝ :=
  action (coordinateKernel KB) (fun x => g a x e) b

/-- Contract the input-only labels after the shared-coordinate action. -/
def rightStage
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ)
    (g : (A → V) → (B → V) → (E → V) → ℝ)
    (y : (A → V) × (B → V)) : ℝ :=
  ∑ e : E → V, (∏ i, KE i (rightCode y i) (e i)) * g y.1 y.2 e

/-- Exact signed action identity; no energy or code hypothesis is used. -/
theorem action_factor
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ)
    (f : ((B → V) × (E → V)) → ℝ)
    (y : (A → V) × (B → V)) :
    action (kernel leftCode rightCode KA KB KE) f y =
      rightStage rightCode KE (middleStage KB (leftStage leftCode KA f)) y := by
  simp only [action, kernel, rightStage, middleStage, leftStage,
    coordinateKernel, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The creation stage uses only the one-coordinate column energies. -/
theorem leftStage_energy
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ) (delta : ℝ)
    (hKA : ∀ a x, (∑ y, KA a y x ^ 2) ≤ delta)
    (f : ((B → V) × (E → V)) → ℝ) :
    (∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
      leftStage leftCode KA f a b e ^ 2) ≤
      delta ^ Fintype.card A * ∑ x, f x ^ 2 := by
  calc
    _ = ∑ b : B → V, ∑ e : E → V, ∑ a : A → V,
        leftStage leftCode KA f a b e ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b : B → V, ∑ e : E → V,
        (∑ a : A → V, (∏ i, KA i (a i) (leftCode (b,e) i)) ^ 2) *
          f (b,e) ^ 2 := by
      simp_rw [leftStage, mul_pow, ← Finset.sum_mul]
    _ ≤ ∑ b : B → V, ∑ e : E → V,
        delta ^ Fintype.card A * f (b,e) ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right
        (AES8.InformationEncoding.remaining_energy KA delta hKA (leftCode (b,e)))
        (sq_nonneg (f (b,e)))
    _ = delta ^ Fintype.card A * ∑ x, f x ^ 2 := by
      simp only [Fintype.sum_prod_type, Finset.mul_sum]

/-- Tensor transport acts on every retained section of a signed joint input. -/
theorem middleStage_energy
    (KB : B → V → V → ℝ) (nu : B → ℝ)
    (hKB : ∀ b g, (∑ y, action (KB b) g y ^ 2) ≤
      nu b ^ 2 * ∑ x, g x ^ 2)
    (g : (A → V) → (B → V) → (E → V) → ℝ) :
    (∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
      middleStage KB g a b e ^ 2) ≤
      (∏ b, nu b) ^ 2 *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V, g a b e ^ 2 := by
  calc
    _ = ∑ a : A → V, ∑ e : E → V, ∑ b : B → V,
        middleStage KB g a b e ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ ≤ ∑ a : A → V, ∑ e : E → V,
        (∏ b, nu b) ^ 2 * ∑ b : B → V, g a b e ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro e _
      exact AESConcrete.FiniteTensorEnergy.coordinate_energy KB nu hKB
        (fun b => g a b e)
    _ = (∏ b, nu b) ^ 2 *
        ∑ a : A → V, ∑ e : E → V, ∑ b : B → V, g a b e ^ 2 := by
      simp only [Finset.mul_sum]
    _ = (∏ b, nu b) ^ 2 *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V, g a b e ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

/-- Contraction uses row energies at the actual output-dependent labels. -/
theorem rightStage_energy
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (delta : ℝ)
    (hKE : ∀ e y, (∑ x, KE e y x ^ 2) ≤ delta)
    (g : (A → V) → (B → V) → (E → V) → ℝ) :
    (∑ y, rightStage rightCode KE g y ^ 2) ≤
      delta ^ Fintype.card E *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V, g a b e ^ 2 := by
  have hpoint (y : (A → V) × (B → V)) :
      rightStage rightCode KE g y ^ 2 ≤
        delta ^ Fintype.card E * ∑ e : E → V, g y.1 y.2 e ^ 2 := by
    calc
      _ ≤ (∑ e : E → V, (∏ i, KE i (rightCode y i) (e i)) ^ 2) *
          ∑ e : E → V, g y.1 y.2 e ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun e : E → V => ∏ i, KE i (rightCode y i) (e i))
          (fun e : E → V => g y.1 y.2 e)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (AES8.InformationEncoding.remaining_energy
          (fun i x z => KE i z x) delta hKE (rightCode y))
        (Finset.sum_nonneg (fun e _ => sq_nonneg (g y.1 y.2 e)))
  calc
    _ ≤ ∑ y : (A → V) × (B → V),
        delta ^ Fintype.card E * ∑ e : E → V, g y.1 y.2 e ^ 2 :=
      Finset.sum_le_sum (fun y _ => hpoint y)
    _ = delta ^ Fintype.card E *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V, g a b e ^ 2 := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type]

/-- The zero-fiber information-overlap estimate with explicit local premises.
The coefficient functions `nu` need not be nonnegative: only their squares
enter this energy statement. The input `f` is arbitrary and signed. -/
theorem information_overlap_energy
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (nu : B → ℝ)
    (hKA : ∀ a x, (∑ y, KA a y x ^ 2) ≤ delta)
    (hKB : ∀ b g, (∑ y, action (KB b) g y ^ 2) ≤
      nu b ^ 2 * ∑ x, g x ^ 2)
    (hKE : ∀ e y, (∑ x, KE e y x ^ 2) ≤ delta)
    (f : ((B → V) × (E → V)) → ℝ) :
    (∑ y, action (kernel leftCode rightCode KA KB KE) f y ^ 2) ≤
      delta ^ (Fintype.card A + Fintype.card E) *
        (∏ b, nu b) ^ 2 * ∑ x, f x ^ 2 := by
  calc
    _ = ∑ y, rightStage rightCode KE
        (middleStage KB (leftStage leftCode KA f)) y ^ 2 := by
      simp only [action_factor]
    _ ≤ delta ^ Fintype.card E *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
          middleStage KB (leftStage leftCode KA f) a b e ^ 2 :=
      rightStage_energy rightCode KE delta hKE _
    _ ≤ delta ^ Fintype.card E * ((∏ b, nu b) ^ 2 *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
          leftStage leftCode KA f a b e ^ 2) :=
      mul_le_mul_of_nonneg_left (middleStage_energy KB nu hKB _)
        (pow_nonneg hd _)
    _ ≤ delta ^ Fintype.card E * ((∏ b, nu b) ^ 2 *
        (delta ^ Fintype.card A * ∑ x, f x ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (leftStage_energy leftCode KA delta hKA f)
          (sq_nonneg (∏ b, nu b))) (pow_nonneg hd _)
    _ = delta ^ (Fintype.card A + Fintype.card E) *
        (∏ b, nu b) ^ 2 * ∑ x, f x ^ 2 := by
      rw [pow_add]
      ring

end AES8.InformationOverlap
