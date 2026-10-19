import AESPaper.ActivityBound
import AESPaper.ResidualMatrix
import AESPaper.WordActivityCoupling

/-!
# Finite Hilbert-space bookkeeping for the actual repeated AES operator
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.PropagationHilbert
open AESMixing AESConcrete AESPaper.ProfileSpace
open AESPaper.BoundaryContraction AESPaper.WordDamping

theorem q_positive : 0 < Assembly.q := by norm_num [Assembly.q]
theorem q_sq_positive : 0 < Assembly.q ^ 2 := pow_pos q_positive _

theorem boundaryLayer_sum {I : Type*} [Fintype I] (f : I → ProfileSpace.State) :
    boundaryLayer (∑ j, f j) = ∑ j, boundaryLayer (f j) := by
  apply PiLp.ext
  intro x
  simp only [boundaryLayer_apply, GroupedRecurrence.Pi_apply,
    WithLp.ofLp_sum, Finset.sum_apply]

theorem sandwich_sum {I : Type*} [Fintype I] (f : I → ProfileSpace.State) :
    sandwich (∑ j, f j) = ∑ j, sandwich (f j) := by
  unfold sandwich
  rw [map_sum, boundaryLayer_sum, map_sum]

/-- One actual two-round step, including its boundary permutation. -/
def halfRound (f : ProfileSpace.State) : ProfileSpace.State :=
  layer (boundaryLayer f)

theorem halfRound_sum {I : Type*} [Fintype I] (f : I → ProfileSpace.State) :
    halfRound (∑ j, f j) = ∑ j, halfRound (f j) := by
  unfold halfRound
  rw [boundaryLayer_sum, map_sum]

theorem halfRound_centered (f : ProfileSpace.State) (hf : Centered f) :
    Centered (halfRound f) :=
  layer_centered _ (boundaryLayer_centered f hf)

theorem halfRound_activity_eq (f : ProfileSpace.State) :
    halfRound (component 0 f) = sandwich (component 0 f) := by
  unfold halfRound sandwich
  rw [layer_activity]

theorem fourRound_eq_halfRound (f : ProfileSpace.State) :
    ConcreteProfile.fourRound f = halfRound (halfRound f) := by
  rw [fourRound_eq_sandwich_boundary]
  rfl

theorem fourRound_sum {I : Type*} [Fintype I] (f : I → ProfileSpace.State) :
    ConcreteProfile.fourRound (∑ j, f j) = ∑ j, ConcreteProfile.fourRound (f j) := by
  simp only [fourRound_eq_sandwich_boundary, boundaryLayer_sum, sandwich_sum]

/-- Projection decomposition followed by the triangle inequality. The map need
not be a kernel operator: preservation of this finite sum is enough. -/
theorem projected_decomposition_bound
    (T : ProfileSpace.State → ProfileSpace.State)
    (hT : ∀ f : Fin 5 → ProfileSpace.State, T (∑ j, f j) = ∑ j, T (f j))
    (f : ProfileSpace.State) (i : Fin 5) :
    ‖component i (T f)‖ ≤ ∑ j, ‖component i (T (component j f))‖ := by
  conv_lhs => rw [← component_decomposition f, hT, map_sum]
  exact norm_sum_le _ _

/-- Cauchy--Schwarz uses the proved orthogonal resolution of the full joint
space; no independence or product-law condition is needed. -/
theorem weighted_profile_cauchy (c : Fin 5 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (f : ProfileSpace.State) :
    (∑ j, c j * profile f j) ≤ Real.sqrt (∑ j, c j ^ 2) * ‖f‖ := by
  have hleft : 0 ≤ ∑ j, c j * profile f j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (profile_nonnegative f j))
  have hsquares : 0 ≤ ∑ j, c j ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  apply (sq_le_sq₀ hleft
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    (∑ j, c j * profile f j) ^ 2 ≤
        (∑ j, c j ^ 2) * ∑ j, profile f j ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (profile f)
    _ = (Real.sqrt (∑ j, c j ^ 2) * ‖f‖) ^ 2 := by
      rw [profile_energy, mul_pow, Real.sq_sqrt hsquares]

/-- The already proved sandwich coefficients, before division by q^2. -/
def sandwichTable (i j : Fin 5) : ℝ :=
  Fin.cases (Fin.cases Assembly.a Assembly.b j)
    (fun i => Fin.cases (Assembly.b i) (Assembly.S i) j) i

theorem sandwichTable_zero_zero : sandwichTable 0 0 = Assembly.a := rfl
theorem sandwichTable_zero_succ (j : Fin 4) :
    sandwichTable 0 j.succ = Assembly.b j := rfl
theorem sandwichTable_succ_zero (i : Fin 4) :
    sandwichTable i.succ 0 = Assembly.b i := rfl
theorem sandwichTable_succ_succ (i j : Fin 4) :
    sandwichTable i.succ j.succ = Assembly.S i j := rfl

theorem sandwichTable_nonnegative (i j : Fin 5) : 0 ≤ sandwichTable i j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · change 0 ≤ Assembly.a
      norm_num [Assembly.a]
    · change 0 ≤ Assembly.b j
      fin_cases j <;> norm_num [Assembly.b, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change 0 ≤ Assembly.b i
      fin_cases i <;> norm_num [Assembly.b, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
    · change 0 ≤ Assembly.S i j
      fin_cases i <;> fin_cases j <;> norm_num [Assembly.S, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

/-- Match the activity-only wrapper to the same actual sandwich used by the
residual and mixed block estimates. -/
theorem sandwich_activity_bound (f : ProfileSpace.State) (hf : Centered f) :
    ‖component 0 (sandwich (component 0 f))‖ ≤
      (Assembly.a / Assembly.q ^ 2) * ‖component 0 f‖ := by
  have he : component 0 (sandwich (component 0 f)) =
      ActivityBound.activitySandwich f := rfl
  rw [he]
  have hq : Assembly.q ^ 2 = (2 : ℝ) ^ 64 := by norm_num [Assembly.q]
  simpa only [Assembly.a, hq] using ActivityBound.activitySandwich_norm f hf

/-- All twenty-five actual sandwich blocks. Only the activity/activity block
requires centering; the hypotheses permit its legal use on every component. -/
theorem sandwich_block (i j : Fin 5) (f : ProfileSpace.State) (hf : Centered f) :
    ‖component i (sandwich (component j f))‖ ≤
      (sandwichTable i j / Assembly.q ^ 2) * ‖component j f‖ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact sandwich_activity_bound f hf
    · exact WordActivityCoupling.sandwich_b_to_activity j f
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact WordActivityCoupling.sandwich_b_from_activity i f
    · exact ResidualMatrix.sandwich_S i j f

theorem sandwich_row_sum (i : Fin 5) (f : ProfileSpace.State) (hf : Centered f) :
    ‖component i (sandwich f)‖ ≤
      (∑ j, sandwichTable i j * profile f j) / Assembly.q ^ 2 := by
  calc
    _ ≤ ∑ j, ‖component i (sandwich (component j f))‖ :=
      projected_decomposition_bound sandwich sandwich_sum f i
    _ ≤ ∑ j, (sandwichTable i j / Assembly.q ^ 2) * profile f j :=
      Finset.sum_le_sum (fun j _ => sandwich_block i j f hf)
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The square-sum row estimate supplying the final input column. -/
theorem sandwich_row_cauchy (i : Fin 5) (f : ProfileSpace.State) (hf : Centered f) :
    ‖component i (sandwich f)‖ ≤
      (Real.sqrt (∑ j, sandwichTable i j ^ 2) / Assembly.q ^ 2) * ‖f‖ := by
  calc
    _ ≤ (∑ j, sandwichTable i j * profile f j) / Assembly.q ^ 2 :=
      sandwich_row_sum i f hf
    _ ≤ (Real.sqrt (∑ j, sandwichTable i j ^ 2) * ‖f‖) / Assembly.q ^ 2 :=
      div_le_div_of_nonneg_right
        (weighted_profile_cauchy (sandwichTable i) (sandwichTable_nonnegative i) f)
        q_sq_positive.le
    _ = _ := by ring

end AESPaper.PropagationHilbert
