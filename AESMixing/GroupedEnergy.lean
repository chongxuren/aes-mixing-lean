import AESMixing.ProductProjection

/-! Regrouping orthogonal components preserves energy exactly. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {I J V : Type*} [Fintype I] [Fintype J] [Fintype V] [DecidableEq J]

def groupedFamily (group : I → J) (f : I → V → ℝ) (j : J) (x : V) : ℝ :=
  ∑ a, if group a = j then f a x else 0

omit [Fintype V] in
theorem groupedFamily_sum (group : I → J) (f : I → V → ℝ) (x : V) :
    (∑ j, groupedFamily group f j x) = ∑ a, f a x := by
  unfold groupedFamily
  rw [Finset.sum_comm]
  simp

omit [Fintype J] in
theorem groupedFamily_energy (group : I → J) (f : I → V → ℝ)
    (ho : ∀ a b, a ≠ b → (∑ x, f a x * f b x) = 0) (j : J) :
    (∑ x, groupedFamily group f j x^2) =
      ∑ a, if group a = j then ∑ x, f a x^2 else 0 := by
  have ho' (a b : I) (hab : a ≠ b) :
      (∑ x, (if group a = j then f a x else 0) *
        (if group b = j then f b x else 0)) = 0 := by
    by_cases ha : group a = j <;> by_cases hb : group b = j <;>
      simp only [ha, hb, if_true, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
    exact ho a b hab
  have he := orthogonal_family_energy (fun a x => if group a = j then f a x else 0) ho'
  change (∑ x, (∑ a, if group a = j then f a x else 0)^2) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : group a = j <;> simp [ha]

theorem groupedFamily_pythagoras (group : I → J) (f : I → V → ℝ)
    (ho : ∀ a b, a ≠ b → (∑ x, f a x * f b x) = 0) :
    (∑ j, ∑ x, groupedFamily group f j x^2) = ∑ a, ∑ x, f a x^2 := by
  simp_rw [groupedFamily_energy group f ho]
  rw [Finset.sum_comm]
  simp

omit [Fintype J] in
theorem groupedFamily_orthogonal (group : I → J) (f : I → V → ℝ)
    (ho : ∀ a b, a ≠ b → (∑ x, f a x * f b x) = 0)
    (i j : J) (hij : i ≠ j) :
    (∑ x, groupedFamily group f i x * groupedFamily group f j x) = 0 := by
  let K : V → I → ℝ := fun x a => if group a = i then f a x else 0
  let L : V → I → ℝ := fun x a => if group a = j then f a x else 0
  have hK : action K (fun _ => 1) = groupedFamily group f i := by
    funext x
    simp [action, K, groupedFamily]
  have hL : action L (fun _ => 1) = groupedFamily group f j := by
    funext x
    simp [action, L, groupedFamily]
  rw [← hK, ← hL, kernel_bilinear]
  have hc (a b : I) : (∑ x, K x a * L x b) = 0 := by
    by_cases ha : group a = i
    · by_cases hb : group b = j
      · have hab : a ≠ b := by
          intro he
          subst b
          exact hij (ha.symm.trans hb)
        simpa only [K, L, ha, hb, if_true] using ho a b hab
      · simp [K, L, hb]
    · simp [K, L, ha]
  simp_rw [hc, mul_zero, Finset.sum_const_zero]

end AESMixing
