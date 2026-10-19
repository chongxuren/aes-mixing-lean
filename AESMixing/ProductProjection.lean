import AESMixing.KernelAlgebra

/-! Orthogonal decomposition by the set of residual coordinate positions.
The vector being decomposed is arbitrary; no product-law assumption occurs. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def productProjection (z : V) (a : I → Bool) (y x : I → V) : ℝ :=
  ∏ i, degreePiece z (a i) (y i) (x i)

omit [DecidableEq I] in
theorem productProjection_symmetric (z : V) (a : I → Bool) (x y : I → V) :
    productProjection z a x y = productProjection z a y x := by
  unfold productProjection
  apply Finset.prod_congr rfl
  intro i _
  exact degreePiece_symmetric z (a i) (x i) (y i)

theorem productProjection_compose (z : V) (hn : 1 < Fintype.card V) (a b : I → Bool) :
    kernelCompose (productProjection z a) (productProjection z b) =
      if a = b then productProjection z a else 0 := by
  funext y x
  have hprod : kernelCompose (productProjection z a) (productProjection z b) y x =
      ∏ i, kernelCompose (degreePiece z (a i)) (degreePiece z (b i)) (y i) (x i) := by
    unfold kernelCompose productProjection
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i v => degreePiece z (a i) (y i) v *
      degreePiece z (b i) v (x i))).symm
  rw [hprod]
  simp_rw [degreePiece_compose z hn]
  by_cases hab : a = b
  · subst b
    simp [productProjection]
  · simp only [hab, if_false, Pi.zero_apply]
    have hw : ∃ i, a i ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem productProjection_sum (z : V) (x y : I → V) :
    (∑ a : I → Bool, productProjection z a x y) = identityKernel x y := by
  change (∑ a : I → Bool, ∏ i, degreePiece z (a i) (x i) (y i)) = _
  rw [← Fintype.prod_sum (fun i b => degreePiece z b (x i) (y i))]
  simp_rw [degreePiece_sum]
  by_cases hxy : x = y
  · subst y
    simp [identityKernel]
  · simp only [identityKernel, hxy, if_false]
    have hw : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i,hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem productProjection_decomposition (z : V) (f : (I → V) → ℝ) :
    (fun x => ∑ a : I → Bool, action (productProjection z a) f x) = f := by
  funext x
  have h : (∑ a : I → Bool, action (productProjection z a) f x) =
      action identityKernel f x := by
    unfold action
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, productProjection_sum]
  rw [h, identityKernel_action]

theorem productProjection_orthogonal (z : V) (hn : 1 < Fintype.card V)
    (a b : I → Bool) (hab : a ≠ b) (f g : (I → V) → ℝ) :
    (∑ y, action (productProjection z a) f y *
      action (productProjection z b) g y) = 0 := by
  rw [kernel_bilinear]
  have hc (x w : I → V) : (∑ y, productProjection z a y x * productProjection z b y w) = 0 := by
    simp_rw [productProjection_symmetric z a _ x]
    change kernelCompose (productProjection z a) (productProjection z b) x w = 0
    rw [productProjection_compose z hn, if_neg hab]
    rfl
  simp_rw [hc, mul_zero, Finset.sum_const_zero]

omit [DecidableEq I] [DecidableEq V] in
theorem orthogonal_family_energy (f : I → V → ℝ)
    (ho : ∀ i j, i ≠ j → (∑ y, f i y * f j y) = 0) :
    (∑ y, (∑ i, f i y)^2) = ∑ i, ∑ y, f i y^2 := by
  classical
  have h := gram_quadratic (fun y i => f i y) (fun _ => 1)
  simp only [mul_one, one_mul, gram] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [pow_two]
  · intro j _ hji
    exact ho i j hji.symm
  · simp

theorem productProjection_pythagoras (z : V) (hn : 1 < Fintype.card V)
    (f : (I → V) → ℝ) :
    (∑ x, f x^2) = ∑ a : I → Bool, ∑ x, action (productProjection z a) f x^2 := by
  have h := orthogonal_family_energy (fun a => action (productProjection z a) f)
    (fun a b hab => productProjection_orthogonal z hn a b hab f f)
  have hd := productProjection_decomposition z f
  simpa only [congrFun hd] using h

end AESMixing
