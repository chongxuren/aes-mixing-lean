import AESMixing.SupportDegreeDecomposition

/-!
# Exact support refinement of whole-word degree projections

An index records the residual mask first and the inactive mask second.
The refined kernel retains residual degree `d` and selects inactive-mask
size `4-a`, so `a` counts active coordinates, including residual ones.
Specializing the generic alphabet to `AES.Word` therefore counts words.

Only exact finite projection algebra is proved. Arbitrary joint real input
functions are permitted, and no quantitative estimate, fourteen-type
completeness statement, attack, or manuscript edit is in scope.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RefinedWordProjection
open AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An exact-support projection, with residual and inactive masks distinct. -/
def supportIndexKernel (z : V) {j : ℕ} (p : SupportIndex j) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  supportProduct z (AES.maskBit p.val.1) (AES.maskBit p.val.2)

theorem supportIndexKernel_action (z : V) {j : ℕ} (p : SupportIndex j)
    (f : (Fin 4 → V) → ℝ) :
    action (supportIndexKernel z p) f = supportIndexComponent z p f := rfl

theorem supportIndexKernel_symmetric (z : V) {j : ℕ} (p : SupportIndex j)
    (x y : Fin 4 → V) : supportIndexKernel z p x y = supportIndexKernel z p y x :=
  supportProduct_symmetric z _ _ x y

/-- The support indices are genuinely distinct orthogonal projections. -/
theorem supportIndexKernel_compose (z : V) (hn : 1 < Fintype.card V)
    {j : ℕ} (p q : SupportIndex j) :
    kernelCompose (supportIndexKernel z p) (supportIndexKernel z q) =
      if p = q then supportIndexKernel z p else 0 := by
  unfold supportIndexKernel
  rw [supportProduct_mixed_compose z hn]
  have heq : (AES.maskBit p.val.1 = AES.maskBit q.val.1 ∧
      AES.maskBit p.val.2 = AES.maskBit q.val.2) ↔ p = q := by
    constructor
    · intro h
      apply Subtype.ext
      exact Prod.ext (maskBits_injective h.1) (maskBits_injective h.2)
    · intro h
      subst q
      exact ⟨rfl, rfl⟩
  by_cases hpq : p = q
  · subst q
    simp
  · have hbits : ¬(AES.maskBit p.val.1 = AES.maskBit q.val.1 ∧
        AES.maskBit p.val.2 = AES.maskBit q.val.2) := by
      intro h
      exact hpq (heq.mp h)
    simp only [hbits, hpq, if_false]

/-- Summing all exact support kernels recovers the existing whole-degree
kernel; this is the kernel form of `supportIndex_decomposition`. -/
theorem supportIndexKernel_sum (z : V) (d : Fin 5) :
    (fun y x => ∑ p : SupportIndex d.val, supportIndexKernel z p y x) =
      degreeKernel z d := by
  apply kernel_action_ext
  intro f
  rw [degreeKernel_action, ← supportIndex_decomposition z d f]
  funext y
  change (∑ x, (∑ p : SupportIndex d.val, supportIndexKernel z p y x) * f x) =
    ∑ p : SupportIndex d.val, action (supportIndexKernel z p) f y
  simp only [action, Finset.sum_mul]
  exact Finset.sum_comm

/-- A whole-degree output projection fixes each of its exact supports. -/
theorem degreeKernel_compose_supportIndexKernel (z : V)
    (hn : 1 < Fintype.card V) (d : Fin 5) (p : SupportIndex d.val) :
    kernelCompose (degreeKernel z d) (supportIndexKernel z p) =
      supportIndexKernel z p := by
  rw [← supportIndexKernel_sum z d]
  funext y x
  unfold kernelCompose
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (q : SupportIndex d.val) :
      (∑ v, supportIndexKernel z q y v * supportIndexKernel z p v x) =
        if q = p then supportIndexKernel z p y x else 0 := by
    have hc := congrFun (congrFun (supportIndexKernel_compose z hn q p) y) x
    by_cases hqp : q = p
    · subst q
      simpa [kernelCompose] using hc
    · simpa [kernelCompose, hqp] using hc
  simp_rw [hterm]
  simp

/-- The matching whole-degree input projection fixes each exact support. -/
theorem supportIndexKernel_compose_degreeKernel (z : V)
    (hn : 1 < Fintype.card V) (d : Fin 5) (p : SupportIndex d.val) :
    kernelCompose (supportIndexKernel z p) (degreeKernel z d) =
      supportIndexKernel z p := by
  rw [← supportIndexKernel_sum z d]
  funext y x
  unfold kernelCompose
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (q : SupportIndex d.val) :
      (∑ v, supportIndexKernel z p y v * supportIndexKernel z q v x) =
        if p = q then supportIndexKernel z p y x else 0 := by
    have hc := congrFun (congrFun (supportIndexKernel_compose z hn p q) y) x
    by_cases hpq : p = q
    · subst q
      simpa [kernelCompose] using hc
    · simpa [kernelCompose, hpq] using hc
  simp_rw [hterm]
  simp

/-- Degree `d` with exactly `a` active coordinates. The active count includes
the residual coordinates; the second support mask records inactivity. -/
def refinedKernel (z : V) (d a : Fin 5) (y x : Fin 4 → V) : ℝ :=
  ∑ p : SupportIndex d.val,
    if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel z p y x else 0

theorem refinedKernel_symmetric (z : V) (d a : Fin 5) (x y : Fin 4 → V) :
    refinedKernel z d a x y = refinedKernel z d a y x := by
  unfold refinedKernel
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact supportIndexKernel_symmetric z p x y
  · simp only [hp, if_false]

/-- The selected support sum remains inside whole degree `d` on output. -/
theorem degreeKernel_compose_refinedKernel (z : V)
    (hn : 1 < Fintype.card V) (d a : Fin 5) :
    kernelCompose (degreeKernel z d) (refinedKernel z d a) =
      refinedKernel z d a := by
  funext y x
  unfold kernelCompose refinedKernel
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact congrFun (congrFun (degreeKernel_compose_supportIndexKernel z hn d p) y) x
  · simp only [hp, if_false, mul_zero, Finset.sum_const_zero]

/-- The selected support sum remains inside whole degree `d` on input. -/
theorem refinedKernel_compose_degreeKernel (z : V)
    (hn : 1 < Fintype.card V) (d a : Fin 5) :
    kernelCompose (refinedKernel z d a) (degreeKernel z d) =
      refinedKernel z d a := by
  funext y x
  unfold kernelCompose refinedKernel
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact congrFun (congrFun (supportIndexKernel_compose_degreeKernel z hn d p) y) x
  · simp only [hp, if_false, zero_mul, Finset.sum_const_zero]

end AESConcrete.RefinedWordProjection
