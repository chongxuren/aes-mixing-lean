import AESMixing.DegreeKernel

/-! Composition of the five actual degree projections. The input vectors
are arbitrary joint functions; no factorization into byte laws is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degreeKernel_cross_gram (z : V) (hn : 1 < Fintype.card V)
    (i j : Fin 5) (x y : Fin 4 → V) :
    (∑ v, degreeKernel z i v x * degreeKernel z j v y) =
      if i = j then degreeKernel z i x y else 0 := by
  unfold degreeKernel
  rw [sum_family_inner]
  have hc (a b : Fin 4 → Bool) :
      (∑ v, (if degreeIndex a = i then productProjection z a v x else 0) *
        (if degreeIndex b = j then productProjection z b v y else 0)) =
      if a = b then
        (if degreeIndex a = i ∧ degreeIndex a = j then productProjection z a x y else 0)
      else 0 := by
    by_cases ha : degreeIndex a = i
    · by_cases hb : degreeIndex b = j
      · simp only [ha, hb, if_true]
        simp_rw [productProjection_symmetric z a _ x]
        change kernelCompose (productProjection z a) (productProjection z b) x y = _
        rw [productProjection_compose z hn]
        by_cases hab : a = b
        · subst b
          simp [ha.symm.trans hb]
        · simp [hab]
      · by_cases hab : a = b
        · subst b
          simp [hb]
        · simp [hb, hab]
    · simp [ha]
  simp_rw [hc]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro a _
    have ha : ¬ (degreeIndex a = i ∧ degreeIndex a = j) := by
      rintro ⟨hi,hj⟩
      exact hij (hi.symm.trans hj)
    simp [ha]

theorem degreeKernel_cross_compose (z : V) (hn : 1 < Fintype.card V)
    (i j : Fin 5) :
    kernelCompose (degreeKernel z i) (degreeKernel z j) =
      if i = j then degreeKernel z i else 0 := by
  funext x y
  unfold kernelCompose
  simp_rw [degreeKernel_symmetric z i x]
  rw [degreeKernel_cross_gram z hn]
  by_cases hij : i = j <;> simp [hij]

theorem degreeComponent_compose (z : V) (hn : 1 < Fintype.card V)
    (i j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z i (degreeComponent z j f) =
      if i = j then degreeComponent z i f else 0 := by
  simp_rw [← degreeKernel_action]
  rw [← kernelCompose_action, degreeKernel_cross_compose z hn]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, if_false]
    funext x
    simp [action]

end AESMixing
