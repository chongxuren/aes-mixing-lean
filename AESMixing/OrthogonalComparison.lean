import AESMixing.L2Sums
import AESMixing.DegreeKernel

/-! Assemble bounds on orthogonal components by their nonnegative scalar
comparison matrix. The input functions may have arbitrary joint dependence. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem l2_orthogonal_sum {A V : Type*} [Fintype A] [Fintype V]
    (f : A → V → ℝ)
    (hf : ∀ a b, a ≠ b → (∑ x, f a x*f b x) = 0) :
    l2 (fun a => l2 (f a)) = l2 (fun x => ∑ a, f a x) := by
  apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  simp only [l2_sq]
  exact (orthogonal_family_energy f hf).symm

theorem orthogonal_bilinear_comparison {A B V : Type*}
    [Fintype A] [Fintype B] [Fintype V]
    (f : B → V → ℝ) (g : A → V → ℝ) (e : V → V)
    (hf : ∀ a b, a ≠ b → (∑ x, f a x*f b x) = 0)
    (hg : ∀ a b, a ≠ b → (∑ x, g a x*g b x) = 0)
    (C : A → B → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hC : ∀ v : B → ℝ, (∑ a, action C v a^2) ≤ c^2 * ∑ b, v b^2)
    (hblock : ∀ a b, |∑ x, g a (e x)*f b x| ≤ C a b*l2 (f b)*l2 (g a)) :
    |∑ x, (∑ a, g a (e x))*(∑ b, f b x)| ≤
      c*l2 (fun x => ∑ b, f b x)*l2 (fun x => ∑ a, g a x) := by
  rw [sum_family_inner]
  calc
    _ ≤ ∑ a, |∑ b, ∑ x, g a (e x)*f b x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |∑ x, g a (e x)*f b x| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, C a b*l2 (f b)*l2 (g a) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hblock a b))
    _ = ∑ a, action C (fun b => l2 (f b)) a*l2 (g a) := by
      simp only [action,Finset.sum_mul]
    _ ≤ l2 (action C (fun b => l2 (f b)))*l2 (fun a => l2 (g a)) :=
      (le_abs_self _).trans (abs_inner_le_l2 _ _)
    _ ≤ (c*l2 (fun b => l2 (f b)))*l2 (fun a => l2 (g a)) :=
      mul_le_mul_of_nonneg_right (l2_le_of_energy _ _ c hc (hC _)) (l2_nonneg _)
    _ = _ := by rw [l2_orthogonal_sum f hf,l2_orthogonal_sum g hg]

end AESMixing
