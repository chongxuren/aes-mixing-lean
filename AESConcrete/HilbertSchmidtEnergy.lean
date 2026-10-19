import AESMixing.L2Sums
import AESMixing.DegreeAdjoint

/-!
# Counting-measure Hilbert--Schmidt identities and ideal inequalities

The matrices may be rectangular. Operator and energy premises stay explicit;
no concrete AES trace or Gram moment is assumed or concluded by this module.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.HilbertSchmidtEnergy
open AESMixing

variable {X Y Z H : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype H]

def hs (A : Y → X → ℝ) : ℝ := l2 (fun p : Y × X => A p.1 p.2)

theorem hs_nonneg (A : Y → X → ℝ) : 0 ≤ hs A := l2_nonneg _

theorem hs_sq (A : Y → X → ℝ) : hs A ^ 2 = ∑ y, ∑ x, A y x ^ 2 := by
  simp only [hs, l2_sq, Fintype.sum_prod_type]

theorem hs_transpose (A : Y → X → ℝ) : hs (fun x y => A y x) = hs A := by
  apply (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).mp
  rw [hs_sq, hs_sq, Finset.sum_comm]

theorem hs_sum_le (A : H → Y → X → ℝ) :
    hs (fun y x => ∑ h, A h y x) ≤ ∑ h, hs (A h) := by
  classical
  exact l2_finset_sum_le Finset.univ (fun h (p : Y × X) => A h p.1 p.2)

theorem transpose_energy (A : Y → X → ℝ) (a : ℝ)
    (hA : ∀ f, (∑ y, action A f y ^ 2) ≤ a^2 * ∑ x, f x^2)
    (g : Y → ℝ) :
    (∑ x, action (fun x y => A y x) g x ^ 2) ≤ a^2 * ∑ y, g y^2 := by
  apply adjoint_energy_le (action A) (action (fun x y => A y x)) a _ hA g
  intro f g
  simp only [action, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem hs_comp_le_left (A : Y → Z → ℝ) (B : Z → X → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hA : ∀ f, (∑ y, action A f y ^ 2) ≤ a^2 * ∑ z, f z^2) :
    hs (kernelCompose A B) ≤ a * hs B := by
  apply (sq_le_sq₀ (hs_nonneg _) (mul_nonneg ha (hs_nonneg _))).mp
  rw [mul_pow, hs_sq, hs_sq, Finset.sum_comm]
  calc
    _ ≤ ∑ x, a^2 * ∑ z, B z x^2 :=
      Finset.sum_le_sum (fun x _ => hA (fun z => B z x))
    _ = a^2 * ∑ z, ∑ x, B z x^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

theorem hs_comp_le_right (A : Y → Z → ℝ) (B : Z → X → ℝ) (b : ℝ)
    (hb : 0 ≤ b)
    (hB : ∀ f, (∑ z, action B f z ^ 2) ≤ b^2 * ∑ x, f x^2) :
    hs (kernelCompose A B) ≤ hs A * b := by
  have ht : (fun x y => kernelCompose A B y x) =
      kernelCompose (fun x z => B z x) (fun z y => A y z) := by
    funext x y
    simp only [kernelCompose, mul_comm]
  rw [← hs_transpose (kernelCompose A B), ht]
  have h := hs_comp_le_left (fun x z => B z x) (fun z y => A y z) b hb
    (transpose_energy B b hB)
  simpa only [hs_transpose, mul_comm] using h

theorem hs_cross_gram_le (A : Y → X → ℝ) (B : Y → Z → ℝ)
    (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ f, (∑ y, action A f y ^ 2) ≤ a^2 * ∑ x, f x^2)
    (hB : ∀ f, (∑ y, action B f y ^ 2) ≤ b^2 * ∑ z, f z^2)
    (hu : hs A ≤ u) (hv : hs B ≤ v) :
    hs (fun x z => ∑ y, A y x * B y z) ≤ min (u*b) (a*v) := by
  apply le_min
  · have h := hs_comp_le_right (fun x y => A y x) B b hb hB
    rw [hs_transpose A] at h
    exact h.trans (mul_le_mul_of_nonneg_right hu hb)
  · exact (hs_comp_le_left (fun x y => A y x) B a ha
      (transpose_energy A a hA)).trans (mul_le_mul_of_nonneg_left hv ha)

theorem hs_gram_block_sum_le (A : H → Y → X → ℝ) (B : H → Y → Z → ℝ)
    (a b u v : H → ℝ) (ha : ∀ h, 0 ≤ a h) (hb : ∀ h, 0 ≤ b h)
    (hA : ∀ h f, (∑ y, action (A h) f y ^ 2) ≤ (a h)^2 * ∑ x, f x^2)
    (hB : ∀ h f, (∑ y, action (B h) f y ^ 2) ≤ (b h)^2 * ∑ z, f z^2)
    (hu : ∀ h, hs (A h) ≤ u h) (hv : ∀ h, hs (B h) ≤ v h) :
    hs (fun x z => ∑ h, ∑ y, A h y x * B h y z) ≤
      ∑ h, min (u h * b h) (a h * v h) := by
  exact (hs_sum_le _).trans (Finset.sum_le_sum (fun h _ =>
    hs_cross_gram_le (A h) (B h) (a h) (b h) (u h) (v h)
      (ha h) (hb h) (hA h) (hB h) (hu h) (hv h)))

end AESConcrete.HilbertSchmidtEnergy
