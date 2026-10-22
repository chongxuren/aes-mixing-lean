import AESConcrete.WeightedDiagonalDominance
import AESConcrete.ActivityEffectiveMetric

/-! Symmetric absolute row bounds control the actual finite quadratic form.
The shifted identity matrix and the sign-sensitive diagonal-dominance theorem
supply the proof; a spectral conclusion is not taken as an assumption. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSymmetricRowQuadratic
open AESConcrete.ActivityEffectiveMetric (qForm)
set_option autoImplicit false
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem quadratic_le (K : I → I → ℝ) (hsym : ∀ i j, K i j = K j i)
    (cap : ℝ) (hrow : ∀ i, (∑ j : I, |K i j|) ≤ cap) (u : I → ℝ) :
    qForm u K ≤ cap * ∑ i : I, (u i)^2 := by
  let M : I → I → ℝ := fun i j => (if i = j then cap else 0) - K i j
  have hM (i j : I) : M i j = M j i := by
    dsimp [M]
    rw [hsym i j]
    by_cases h : i = j
    · subst j; rfl
    · simp [h, Ne.symm h]
  have hdom (i : I) :
      (∑ j : I, if i = j then 0 else |M i j| * (1 : ℝ)) ≤ M i i * 1 := by
    have he : (∑ j : I, if i = j then 0 else |K i j|) + |K i i| =
        ∑ j : I, |K i j| := by
      calc
        _ = ∑ j : I, ((if i = j then 0 else |K i j|) +
            (if i = j then |K i i| else 0)) := by
          simp [Finset.sum_add_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : i = j
          · subst j; simp
          · simp [h]
    have hb := hrow i
    have ha := le_abs_self (K i i)
    have hm : (∑ j : I, if i = j then 0 else |M i j| * 1) =
        ∑ j : I, if i = j then 0 else |K i j| := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [M, h]
    rw [hm]
    dsimp [M]
    simp only [if_true, mul_one]
    linarith
  have hp := AESConcrete.WeightedDiagonalDominance.weighted_diagonal_nonneg M
    (fun _ => 1) hM (fun _ => by norm_num) hdom u
  have he : qForm u M = cap * ∑ i : I, (u i)^2 - qForm u K := by
    unfold qForm
    simp only [M, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change 0 ≤ qForm u M at hp
  rw [he] at hp
  linarith

end AES8.PaperSymmetricRowQuadratic
