import AESPaper.PropagationHilbert
import AESPaper.UniversalInitialization

/-!
# Conditional assembly of the fixed five-component propagation bound

The only analytic hypotheses in this file are the exact raw-boundary C table
and the residual-to-activity t column. They concern the actual `boundaryLayer`
and arbitrary signed joint inputs. The proved S, b, a, word damping, orthogonal
resolution and initialization supply every other step. The raw t estimates in
the opposite direction are not needed by this composition.

Editorial: the activity input is propagated through H Pi first, then split;
positive output degrees receive their last-layer damping. For inputs of degree
1--3, split the right Pi before applying H Pi H. For degree 4, use the orthogonal
square sum. These choices are necessary to match all twenty-five printed
rounding inequalities. No propagation inequality is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.FiveComponentPropagation
open AESMixing AESConcrete AESPaper.ProfileSpace
open AESPaper.WordDamping AESPaper.BoundaryContraction
open AESPaper.PropagationHilbert

/-- The positive-input blocks of the final H Pi, with output damping kept. -/
def residualBoundaryTable (i : Fin 5) (j : Fin 4) : ℝ :=
  Fin.cases (Assembly.t j)
    (fun i => WordDamping.nu ^ (i.val + 1) * Assembly.C i j) i

theorem residualBoundaryTable_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ residualBoundaryTable i j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change 0 ≤ Assembly.t j
    fin_cases j <;> norm_num [Assembly.t, Assembly.q, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  · change 0 ≤ WordDamping.nu ^ (i.val + 1) * Assembly.C i j
    apply mul_nonneg (pow_nonneg WordDamping.nu_nonnegative _)
    fin_cases i <;> fin_cases j <;> norm_num [Assembly.C, Assembly.q,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]

/-- Four-round coefficient for activity input, before the common q^-2. -/
def activityColumn (i : Fin 5) : ℝ :=
  sandwichTable i 0 * Assembly.a / Assembly.q ^ 2 +
    ∑ l, residualBoundaryTable i l * Assembly.b l

/-- Four-round coefficient for residual input of degree 1--3. -/
def smallColumn (i : Fin 5) (j : Fin 3) : ℝ :=
  sandwichTable i 0 * Assembly.t j.castSucc +
    ∑ l, sandwichTable i l.succ * Assembly.C l j.castSucc

/-- The last column uses the Euclidean length of the sandwich row. -/
def lastColumn (i : Fin 5) : ℝ :=
  Real.sqrt (∑ j, sandwichTable i j ^ 2)

theorem activityColumn_zero :
    activityColumn 0 = Assembly.a ^ 2 / Assembly.q ^ 2 +
      ∑ l, Assembly.b l * Assembly.t l := by
  unfold activityColumn
  change Assembly.a * Assembly.a / Assembly.q ^ 2 +
    (∑ l, Assembly.t l * Assembly.b l) = _
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

theorem activityColumn_succ (i : Fin 4) :
    activityColumn i.succ =
      Assembly.a * Assembly.b i / Assembly.q ^ 2 +
        Assembly.nu ^ (i.val + 1) * (∑ l, Assembly.C i l * Assembly.b l) := by
  unfold activityColumn
  change Assembly.b i * Assembly.a / Assembly.q ^ 2 +
    (∑ l, WordDamping.nu ^ (i.val + 1) * Assembly.C i l * Assembly.b l) = _
  have hn : WordDamping.nu = Assembly.nu := rfl
  rw [hn, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

theorem activityColumn_round (i : Fin 5) :
    activityColumn i < Assembly.roundedEntry i 0 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [activityColumn_zero]
    exact Assembly.activity_activity
  · rw [activityColumn_succ]
    exact Assembly.residual_activity i

theorem smallColumn_round (i : Fin 5) (j : Fin 3) :
    smallColumn i j < Assembly.roundedEntry i j.castSucc.succ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Assembly.activity_residual j
  · exact Assembly.residual_residual i j

theorem lastColumn_round (i : Fin 5) :
    lastColumn i < Assembly.roundedEntry i 4 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [lastColumn, Fin.sum_univ_succ, sandwichTable_zero_zero,
      sandwichTable_zero_succ] using Assembly.activity_last
  · simpa only [lastColumn, Fin.sum_univ_succ, sandwichTable_succ_zero,
      sandwichTable_succ_succ] using Assembly.residual_last i

section RawBoundary

variable
    (hC : ∀ (i j : Fin 4) (f : ProfileSpace.State),
      ‖component i.succ (boundaryLayer (component j.succ f))‖ ≤
        Assembly.C i j * ‖component j.succ f‖)
    (ht : ∀ (j : Fin 4) (f : ProfileSpace.State),
      ‖component 0 (boundaryLayer (component j.succ f))‖ ≤
        Assembly.t j * ‖component j.succ f‖)

/-- The activity input to H Pi equals its input to the proved H Pi H block. -/
theorem halfRound_activity_block (i : Fin 5) (f : ProfileSpace.State)
    (hf : Centered f) :
    ‖component i (halfRound (component 0 f))‖ ≤
      (sandwichTable i 0 / Assembly.q ^ 2) * ‖component 0 f‖ := by
  rw [halfRound_activity_eq]
  exact sandwich_block i 0 f hf

include hC ht in
/-- Raw positive-input blocks followed by the final layer. This is the place
where residual output degrees retain their essential factor nu^i. -/
theorem halfRound_residual_block (i : Fin 5) (j : Fin 4)
    (f : ProfileSpace.State) :
    ‖component i (halfRound (component j.succ f))‖ ≤
      residualBoundaryTable i j * ‖component j.succ f‖ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · unfold halfRound
    rw [activity_layer]
    exact ht j f
  · unfold halfRound
    rw [← layer_component]
    calc
      _ ≤ WordDamping.nu ^ i.succ.val *
          ‖component i.succ (boundaryLayer (component j.succ f))‖ :=
        layer_component_norm i.succ _
      _ ≤ WordDamping.nu ^ i.succ.val *
          (Assembly.C i j * ‖component j.succ f‖) :=
        mul_le_mul_of_nonneg_left (hC i j f)
          (pow_nonneg nu_nonnegative _)
      _ = _ := by
        change _ =
          (WordDamping.nu ^ (i.val + 1) * Assembly.C i j) * ‖component j.succ f‖
        simp only [Fin.val_succ]
        ring

include hC ht in
theorem halfRound_row (i : Fin 5) (f : ProfileSpace.State) (hf : Centered f) :
    ‖component i (halfRound f)‖ ≤
      (sandwichTable i 0 / Assembly.q ^ 2) * profile f 0 +
        ∑ l, residualBoundaryTable i l * profile f l.succ := by
  calc
    _ ≤ ∑ j, ‖component i (halfRound (component j f))‖ :=
      projected_decomposition_bound halfRound halfRound_sum f i
    _ = ‖component i (halfRound (component 0 f))‖ +
        ∑ l : Fin 4, ‖component i (halfRound (component l.succ f))‖ :=
      Fin.sum_univ_succ _
    _ ≤ _ := add_le_add (halfRound_activity_block i f hf)
      (Finset.sum_le_sum (fun l _ => halfRound_residual_block hC ht i l f))

include hC ht in
/-- Activity input: split the first H Pi output, not the rightmost Pi output.
This combines the proved b table with final raw-C damping. -/
theorem fourRound_activity_block (i : Fin 5) (f : ProfileSpace.State)
    (hf : Centered f) :
    ‖component i (ConcreteProfile.fourRound (component 0 f))‖ ≤
      (activityColumn i / Assembly.q ^ 2) * ‖component 0 f‖ := by
  let g := halfRound (component 0 f)
  have hg : Centered g := halfRound_centered _ (component_centered 0 f hf)
  have h0 : profile g 0 ≤ (Assembly.a / Assembly.q ^ 2) * ‖component 0 f‖ :=
    halfRound_activity_block 0 f hf
  have hr (l : Fin 4) :
      profile g l.succ ≤ (Assembly.b l / Assembly.q ^ 2) * ‖component 0 f‖ :=
    halfRound_activity_block l.succ f hf
  rw [fourRound_eq_halfRound]
  change ‖component i (halfRound g)‖ ≤ _
  calc
    _ ≤ (sandwichTable i 0 / Assembly.q ^ 2) * profile g 0 +
        ∑ l, residualBoundaryTable i l * profile g l.succ :=
      halfRound_row hC ht i g hg
    _ ≤ (sandwichTable i 0 / Assembly.q ^ 2) *
          ((Assembly.a / Assembly.q ^ 2) * ‖component 0 f‖) +
        ∑ l, residualBoundaryTable i l *
          ((Assembly.b l / Assembly.q ^ 2) * ‖component 0 f‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left h0
          (div_nonneg (sandwichTable_nonnegative i 0) q_sq_positive.le)
      · exact Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hr l) (residualBoundaryTable_nonnegative i l))
    _ = _ := by
      unfold activityColumn
      simp only [add_div, add_mul, Finset.sum_div, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro l _
        ring

include hC ht in
/-- Residual inputs of degrees 1--3: split the right boundary first, so the
proved sandwich S and b estimates can be applied to each resulting degree. -/
theorem fourRound_small_block (i : Fin 5) (j : Fin 3)
    (f : ProfileSpace.State) (hf : Centered f) :
    ‖component i (ConcreteProfile.fourRound (component j.castSucc.succ f))‖ ≤
      (smallColumn i j / Assembly.q ^ 2) * ‖component j.castSucc.succ f‖ := by
  let g := boundaryLayer (component j.castSucc.succ f)
  have hg : Centered g := boundaryLayer_centered _
    (component_centered j.castSucc.succ f hf)
  have h0 : profile g 0 ≤ Assembly.t j.castSucc * ‖component j.castSucc.succ f‖ :=
    ht j.castSucc f
  have hr (l : Fin 4) :
      profile g l.succ ≤ Assembly.C l j.castSucc * ‖component j.castSucc.succ f‖ :=
    hC l j.castSucc f
  rw [fourRound_eq_sandwich_boundary]
  change ‖component i (sandwich g)‖ ≤ _
  calc
    _ ≤ (∑ k, sandwichTable i k * profile g k) / Assembly.q ^ 2 :=
      sandwich_row_sum i g hg
    _ = (sandwichTable i 0 * profile g 0 +
        ∑ l : Fin 4, sandwichTable i l.succ * profile g l.succ) / Assembly.q ^ 2 := by
      rw [Fin.sum_univ_succ]
    _ ≤ (sandwichTable i 0 *
          (Assembly.t j.castSucc * ‖component j.castSucc.succ f‖) +
        ∑ l, sandwichTable i l.succ *
          (Assembly.C l j.castSucc * ‖component j.castSucc.succ f‖)) /
        Assembly.q ^ 2 := by
      apply div_le_div_of_nonneg_right _ q_sq_positive.le
      exact add_le_add (mul_le_mul_of_nonneg_left h0 (sandwichTable_nonnegative i 0))
        (Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hr l) (sandwichTable_nonnegative i l.succ)))
    _ = _ := by
      unfold smallColumn
      simp only [add_div, add_mul, Finset.sum_div, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro l _
        ring

/-- Degree-four input: preserve the orthogonal square sum and boundary
isometry, instead of separately capping five boundary projections. -/
theorem fourRound_last_block (i : Fin 5) (f : ProfileSpace.State)
    (hf : Centered f) :
    ‖component i (ConcreteProfile.fourRound (component 4 f))‖ ≤
      (lastColumn i / Assembly.q ^ 2) * ‖component 4 f‖ := by
  rw [fourRound_eq_sandwich_boundary]
  calc
    _ ≤ (lastColumn i / Assembly.q ^ 2) *
        ‖boundaryLayer (component 4 f)‖ :=
      sandwich_row_cauchy i _
        (boundaryLayer_centered _ (component_centered 4 f hf))
    _ = _ := by rw [boundaryLayer_norm]

include hC ht in
/-- The rounded 25-block estimate. All nonlinear or degree-sensitive work has
already been discharged above; this step uses the printed exact arithmetic. -/
theorem fourRound_block_rounded (i j : Fin 5) (f : ProfileSpace.State)
    (hf : Centered f) :
    ‖component i (ConcreteProfile.fourRound (component j f))‖ ≤
      (Assembly.roundedEntry i j / Assembly.q ^ 2) * ‖component j f‖ := by
  fin_cases j
  · exact (fourRound_activity_block hC ht i f hf).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (activityColumn_round i).le q_sq_positive.le)
        (norm_nonneg _))
  · exact (fourRound_small_block hC ht i 0 f hf).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (smallColumn_round i 0).le q_sq_positive.le)
        (norm_nonneg _))
  · exact (fourRound_small_block hC ht i 1 f hf).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (smallColumn_round i 1).le q_sq_positive.le)
        (norm_nonneg _))
  · exact (fourRound_small_block hC ht i 2 f hf).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (smallColumn_round i 2).le q_sq_positive.le)
        (norm_nonneg _))
  · exact (fourRound_last_block i f hf).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (lastColumn_round i).le q_sq_positive.le)
        (norm_nonneg _))

include hC ht in
theorem fourRound_profile (f : ProfileSpace.State) (hf : Centered f) (i : Fin 5) :
    profile (ConcreteProfile.fourRound f) i ≤
      ∑ j, (Assembly.roundedEntry i j / Assembly.q ^ 2) * profile f j := by
  exact (projected_decomposition_bound ConcreteProfile.fourRound fourRound_sum f i).trans
    (Finset.sum_le_sum (fun j _ => fourRound_block_rounded hC ht i j f hf))

/-- Exact conversion of the unnormalized rounded row to the fixed recurrence.
The row and column weights, and the common q^2=2^64, are all retained. -/
theorem rounded_row_normalization (f : ProfileSpace.State) (i : Fin 5) :
    ((2 : ℝ) ^ 80 *
      (∑ j, (Assembly.roundedEntry i j / Assembly.q ^ 2) * profile f j)) /
      AESPaper.weights i = AESPaper.step (normalizedProfile f) i := by
  have hwi : AESPaper.weights i ≠ 0 := ne_of_gt (weights_positive i)
  have hq : Assembly.q ^ 2 = (2 : ℝ) ^ 64 := by norm_num [Assembly.q]
  unfold AESPaper.step normalizedProfile Assembly.roundedEntry
  rw [hq]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hwj : AESPaper.weights j ≠ 0 := ne_of_gt (weights_positive j)
  field_simp [hwi, hwj]

include hC ht in
/-- Uniform repeated-operator estimate on every signed centered joint input.
This theorem assumes precisely two raw-boundary table APIs, not propagation. -/
theorem operator (f : ProfileSpace.State) (hf : Centered f) (i : Fin 5) :
    normalizedProfile (ConcreteProfile.fourRound f) i ≤
      AESPaper.step (normalizedProfile f) i := by
  unfold normalizedProfile
  calc
    _ ≤ ((2 : ℝ) ^ 80 *
        (∑ j, (Assembly.roundedEntry i j / Assembly.q ^ 2) * profile f j)) /
        AESPaper.weights i :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fourRound_profile hC ht f hf i) (by positivity))
        (weights_positive i).le
    _ = _ := rounded_row_normalization f i

include hC ht in
/-- Conditional fixed-target consequence with proved universal initialization.
The raw-boundary tables must still be instantiated before this is unconditional. -/
theorem epsilon_bound (k r : ℕ) (hr : 4 + 4 * k ≤ r) :
    AESMixing.AES.epsilon r < rationalBound k ∧ rationalBound k < decimalBound k :=
  ConcreteProfile.epsilon_of_initialization_and_operator
    UniversalInitialization.physical_initial (operator hC ht) k r hr

end RawBoundary
end AESPaper.FiveComponentPropagation
