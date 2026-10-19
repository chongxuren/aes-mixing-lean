import AESMixing.CommonSource
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Real finite-dimensional product columns. The number of extra factors is
arbitrary; this is the real-coordinate specialization needed for AES. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {ι α β γ η : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [Fintype γ] [Fintype η] [DecidableEq η]

theorem product_column_energy (C : η → γ → ℝ) :
    (∑ y : η → γ, (∏ t, C t (y t)) ^ 2) = ∏ t, ∑ z, C t z ^ 2 := by
  simp_rw [← Finset.prod_pow]
  exact (Fintype.prod_sum (fun t z => C t z ^ 2)).symm

theorem product_column_energy_le (C : η → γ → ℝ) (delta : ℝ)
    (hC : ∀ t, ∑ z, C t z ^ 2 ≤ delta) :
    (∑ y : η → γ, (∏ t, C t (y t)) ^ 2) ≤ delta ^ Fintype.card η := by
  rw [product_column_energy]
  calc
    (∏ t, ∑ z, C t z ^ 2) ≤ ∏ _ : η, delta :=
      Finset.prod_le_prod
        (fun t _ => Finset.sum_nonneg (fun z _ => sq_nonneg (C t z)))
        (fun t _ => hC t)
    _ = delta ^ Fintype.card η := by simp

/-- One bounded operator, one trace bound, and any number of diagonal bounds. -/
theorem capped_common_source (A : α → ι → ℝ) (B : β → ι → ℝ)
    (C : η → γ → ι → ℝ) (mu : ι → ℝ) (nu p h delta : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hA : ∀ x : ι → ℝ,
      (∑ a, (∑ i, A a i * x i) ^ 2) ≤ nu ^ 2 * ∑ i, x i ^ 2)
    (hmu : ∀ i, |mu i| ≤ p)
    (hB : (∑ i, ∑ b, B b i ^ 2) ≤ h)
    (hC : ∀ t i, ∑ z, C t z i ^ 2 ≤ delta) :
    (∑ y : β × (η → γ), ∑ a,
      (∑ i, A a i * (mu i * (B y.1 i * ∏ t, C t (y.2 t) i))) ^ 2) ≤
      nu ^ 2 * p ^ 2 * (h * delta ^ Fintype.card η) := by
  apply capped_common_source_two (β := β × (η → γ)) A
    (fun (y : β × (η → γ)) i => B y.1 i * ∏ t, C t (y.2 t) i)
    mu nu p (h * delta ^ Fintype.card η) hp hA hmu
  have hpoint (i : ι) :
      (∑ y : β × (η → γ), (B y.1 i * ∏ t, C t (y.2 t) i) ^ 2) ≤
        (∑ b, B b i ^ 2) * delta ^ Fintype.card η := by
    simp only [Fintype.sum_prod_type, mul_pow]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (product_column_energy_le (fun t z => C t z i) delta (fun t => hC t i))
      (Finset.sum_nonneg (fun b _ => sq_nonneg (B b i)))
  calc
    (∑ i, ∑ y : β × (η → γ), (B y.1 i * ∏ t, C t (y.2 t) i) ^ 2)
        ≤ ∑ i, (∑ b, B b i ^ 2) * delta ^ Fintype.card η :=
          Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i, ∑ b, B b i ^ 2) * delta ^ Fintype.card η := by
      rw [Finset.sum_mul]
    _ ≤ h * delta ^ Fintype.card η :=
      mul_le_mul_of_nonneg_right hB (pow_nonneg hd _)

end AESMixing
