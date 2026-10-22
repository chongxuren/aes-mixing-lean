/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.PaperSupportProjection

/-! Kernel and idempotence laws for the genuine grouped tensor projections. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AES8.PaperSupportProjection
open AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def kernel (z : V) (i t : ℕ) (y x : Fin n → V) : ℝ :=
  ∑ p : Label n, if residualCount p.1 = i ∧ supportCount p.2 = t
    then supportProduct z p.1 p.2 y x else 0

theorem component_eq_action (z : V) (f : (Fin n → V) → ℝ) (i t : ℕ) :
    component z f i t = action (kernel z i t) f := by
  funext y
  unfold component raw action kernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem kernel_symmetric (z : V) (i t : ℕ) (y x : Fin n → V) :
    kernel z i t y x = kernel z i t x y := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · exact supportProduct_symmetric z p.1 p.2 y x
  · rfl

theorem raw_compose (z : V) (hq : 1 < Fintype.card V)
    (p q : Label n) (f : (Fin n → V) → ℝ) :
    raw z p (raw z q f) = if p = q then raw z p f else 0 := by
  unfold raw
  rw [← kernelCompose_action, supportProduct_mixed_compose z hq]
  by_cases hpq : p = q
  · subst q
    simp
  · have h : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun h => hpq (Prod.ext h.1 h.2)
    simp only [h, hpq, if_false]
    exact zero_kernel_action f

theorem raw_component (z : V) (hq : 1 < Fintype.card V)
    (p : Label n) (f : (Fin n → V) → ℝ) (j u : ℕ) (x : Fin n → V) :
    raw z p (component z f j u) x =
      if residualCount p.1 = j ∧ supportCount p.2 = u then raw z p f x else 0 := by
  have hex : raw z p (component z f j u) x =
      ∑ q : Label n, if residualCount q.1 = j ∧ supportCount q.2 = u
        then raw z p (raw z q f) x else 0 := by
    unfold raw action component
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp [raw, action, Finset.mul_sum]
  rw [hex]
  simp_rw [raw_compose z hq]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [Ne.symm hqp]
  · simp

theorem component_compose (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (i t j u : ℕ) :
    component z (component z f j u) i t =
      if (i,t) = (j,u) then component z f i t else 0 := by
  funext x
  change (∑ p : Label n, if residualCount p.1 = i ∧ supportCount p.2 = t
      then raw z p (component z f j u) x else 0) =
    (if (i,t) = (j,u) then component z f i t else 0) x
  simp_rw [raw_component z hq]
  by_cases hij : (i,t) = (j,u)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
    rw [if_pos rfl]
    change (∑ p : Label n, if residualCount p.1 = i ∧ supportCount p.2 = t then
        (if residualCount p.1 = i ∧ supportCount p.2 = t then raw z p f x else 0) else 0) =
      ∑ p : Label n, if residualCount p.1 = i ∧ supportCount p.2 = t then raw z p f x else 0
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : residualCount p.1 = i ∧ supportCount p.2 = t <;>
      simp [hp]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : residualCount p.1 = i ∧ supportCount p.2 = t
    · have hp' : ¬(residualCount p.1 = j ∧ supportCount p.2 = u) := by
        intro h
        exact hij (Prod.ext (hp.1.symm.trans h.1) (hp.2.symm.trans h.2))
      rw [if_pos hp, if_neg hp']
    · rw [if_neg hp]

theorem component_idempotent (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (i t : ℕ) :
    component z (component z f i t) i t = component z f i t := by
  simpa using component_compose z hq f i t i t

theorem kernel_compose (z : V) (hq : 1 < Fintype.card V) (i t j u : ℕ) :
    kernelCompose (kernel (n := n) z i t) (kernel z j u) =
      if (i,t) = (j,u) then kernel z i t else 0 := by
  apply kernel_action_ext _ _
  intro f
  rw [kernelCompose_action, ← component_eq_action, ← component_eq_action,
    component_compose z hq]
  by_cases h : (i,t) = (j,u)
  · simp [h, component_eq_action]
  · simp [h, zero_kernel_action]

end AES8.PaperSupportProjection
