import AESPaper.Comparison
import AESConcrete.KernelOperator
import AESMixing.DegreeComposition
import AESMixing.DegreeCentering
import AESMixing.DegreeProjectionBounds
import AESMixing.ActivitySpan

/-!
# The v9 five-component profile on actual AES word states

All vectors use counting-measure Euclidean norm on the full `AES.WordState`.
The paper's nonzero-state vectors are represented by zero extension; `Centered`
records both the zero distinguished coordinate and zero total mass.  Degree
here counts residual 32-bit words, rather than residual bytes inside one word.

Index 0 is the activity projection; indices 1--4 are the four residual degrees.
The activity projection on the full space also contains stationary directions.
Only its restriction to `Centered` is the paper's centered activity component.
-/

set_option autoImplicit false
-- Concrete word-state coercions exceed Lean's default elaborator recursion depth.
set_option maxRecDepth 10000
open scoped BigOperators
noncomputable section

namespace AESPaper.ProfileSpace
open AESMixing AESConcrete

abbrev State := EuclideanSpace ℝ AES.WordState

/-- Zero extension of the paper's centered nonzero-state space. -/
def Centered (f : State) : Prop := f 0 = 0 ∧ (∑ x, f x) = 0

theorem word_card_gt_one : 1 < Fintype.card AES.Word := by
  rw [AES.word_card]
  norm_num

/-- Actual continuous linear degree projection, with 0 denoting activity. -/
def component (i : Fin 5) : State →L[ℝ] State :=
  kernelOperator (degreeKernel (0 : AES.Word) i)

theorem component_apply (i : Fin 5) (f : State) (x : AES.WordState) :
    component i f x = degreeComponent (0 : AES.Word) i (fun y => f y) x := by
  unfold component
  rw [kernelOperator_apply, degreeKernel_action]

/-- The paper's `x(f)`, in the order activity,1,2,3,4. -/
def profile (f : State) : AESPaper.Profile := fun i => ‖component i f‖

theorem profile_nonnegative (f : State) (i : Fin 5) : 0 ≤ profile f i :=
  norm_nonneg _

theorem l2_eq_norm (f : State) : AESMixing.l2 (fun x => f x) = ‖f‖ := by
  unfold AESMixing.l2
  rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

/-- The projections resolve the identity even before restricting to centered vectors. -/
theorem component_decomposition (f : State) : (∑ i, component i f) = f := by
  ext x
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, component_apply]
  exact congrFun (degreeComponent_decomposition (0 : AES.Word) (fun y => f y)) x

theorem component_compose (i j : Fin 5) (f : State) :
    component i (component j f) = if i = j then component i f else 0 := by
  have h := degreeComponent_compose (0 : AES.Word) word_card_gt_one i j (fun y => f y)
  by_cases hij : i = j
  · rw [if_pos hij]
    ext x
    simp only [component_apply]
    have hx := congrFun h x
    rw [if_pos hij] at hx
    exact hx
  · rw [if_neg hij]
    ext x
    change component i (component j f) x = (0 : ℝ)
    simp only [component_apply]
    have hx := congrFun h x
    rw [if_neg hij] at hx
    exact hx

theorem component_idempotent (i : Fin 5) (f : State) :
    component i (component i f) = component i f := by
  simpa using component_compose i i f

/-- Orthogonality holds for two arbitrary joint inputs, with no independence premise. -/
theorem component_cross_orthogonal (i j : Fin 5) (hij : i ≠ j) (f g : State) :
    (∑ x, component i f x * component j g x) = 0 := by
  simp only [component_apply, ← degreeKernel_action]
  rw [kernel_bilinear]
  simp_rw [degreeKernel_cross_gram (0 : AES.Word) word_card_gt_one i j,
    if_neg hij, mul_zero, Finset.sum_const_zero]

theorem component_inner_orthogonal (i j : Fin 5) (hij : i ≠ j) (f g : State) :
    inner ℝ (component i f) (component j g) = 0 := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  exact component_cross_orthogonal i j hij f g

/-- Sum of the five squared lengths is the actual counting-measure squared norm. -/
theorem profile_energy (f : State) : (∑ i, profile f i ^ 2) = ‖f‖ ^ 2 := by
  simpa only [profile, EuclideanSpace.real_norm_sq_eq, component_apply] using
    degreeComponent_pythagoras (0 : AES.Word) word_card_gt_one (fun y => f y)

theorem component_norm_le (i : Fin 5) : ‖component i‖ ≤ 1 := by
  apply kernelOperator_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa only [degreeKernel_action, one_pow, _root_.one_mul] using
    degreeComponent_energy_le (0 : AES.Word) word_card_gt_one i f

/-- Each of the five components remains in the paper's centered space. -/
theorem component_centered (i : Fin 5) (f : State) (hf : Centered f) :
    Centered (component i f) := by
  have h :=
    degreeComponent_centered (0 : AES.Word) word_card_gt_one i (fun y => f y) hf.1 hf.2
  have hz : (fun _ : Fin 4 => (0 : AES.Word)) = (0 : AES.WordState) := by
    funext x
    rfl
  constructor
  · simpa only [component_apply, hz] using h.1
  · simpa only [component_apply] using h.2

/-- Two states have the same zero/nonzero pattern of 32-bit words. -/
def SameActivity (x y : AES.WordState) : Prop := ∀ i, (x i = 0 ↔ y i = 0)

theorem activity_kernel_same_pattern (x y z : AES.WordState) (hxy : SameActivity x y) :
    degreeKernel (0 : AES.Word) 0 x z = degreeKernel (0 : AES.Word) 0 y z := by
  simp only [degreeKernel_zero, productProjection]
  apply Finset.prod_congr rfl
  intro i _
  change activityMatrix (0 : AES.Word) (x i) (z i) =
    activityMatrix (0 : AES.Word) (y i) (z i)
  by_cases hx : x i = 0
  · have hy : y i = 0 := (hxy i).mp hx
    simp only [activityMatrix, hx, hy, if_true]
  · have hy : y i ≠ 0 := fun hy => hx ((hxy i).mpr hy)
    simp only [activityMatrix, hx, hy, if_false]

/-- Degree zero is constant on every zero/nonzero word-pattern cell. -/
theorem activity_same_pattern (f : State) (x y : AES.WordState)
    (hxy : SameActivity x y) : component 0 f x = component 0 f y := by
  rw [component_apply, component_apply]
  simp only [← degreeKernel_action]
  unfold action
  simp_rw [activity_kernel_same_pattern x y _ hxy]

theorem activity_constant_on_allActive (f : State) (x y : AES.WordState)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) :
    component 0 f x = component 0 f y := by
  apply activity_same_pattern f x y
  intro i
  exact iff_of_false (hx i) (hy i)

/-- Removing activity leaves exactly the four positive residual degrees. -/
theorem component_sub_activity (i : Fin 5) (f : State) :
    component i (f - component 0 f) = if i = 0 then 0 else component i f := by
  rw [map_sub, component_compose]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi]

theorem residual_norm_sq (f : State) :
    ‖f - component 0 f‖ ^ 2 = ∑ i : Fin 4, profile f i.succ ^ 2 := by
  have h := profile_energy (f - component 0 f)
  rw [Fin.sum_univ_succ] at h
  simpa [profile, component_sub_activity] using h.symm

theorem residual_norm (f : State) :
    ‖f - component 0 f‖ = Real.sqrt (∑ i : Fin 4, profile f i.succ ^ 2) := by
  rw [← residual_norm_sq f, Real.sqrt_sq (norm_nonneg _)]

/-- The exact normalization used by `PhysicalInterface` and v9 Appendix D. -/
def normalizedProfile (f : State) : AESPaper.Profile :=
  fun i => (2 : ℝ) ^ 80 * profile f i / AESPaper.weights i

theorem weights_positive (i : Fin 5) : 0 < AESPaper.weights i := by
  fin_cases i <;> norm_num [AESPaper.weights]

theorem normalizedProfile_nonnegative (f : State) (i : Fin 5) :
    0 ≤ normalizedProfile f i :=
  div_nonneg (mul_nonneg (by positivity) (profile_nonnegative f i))
    (weights_positive i).le

theorem normalization (f : State) (i : Fin 5) :
    AESPaper.weights i * normalizedProfile f i = (2 : ℝ) ^ 80 * profile f i := by
  unfold normalizedProfile
  field_simp [ne_of_gt (weights_positive i)]

/-- The scalar score is exactly the paper's activity-sensitive norm after scaling. -/
theorem score_normalization (f : State) :
    AESPaper.score (normalizedProfile f) = (2 : ℝ) ^ 80 *
      (profile f 0 / 16384 + Real.sqrt (∑ i : Fin 4, profile f i.succ ^ 2)) := by
  let c : ℝ := (2 : ℝ) ^ 80
  have hc : 0 ≤ c := by positivity
  have h0 : (4096 : ℝ) * normalizedProfile f 0 = c * profile f 0 :=
    normalization f 0
  have hA : normalizedProfile f 0 / 4 = c * (profile f 0 / 16384) := by
    nlinarith [h0]
  have h1 : (5 : ℝ) * normalizedProfile f 1 = c * profile f 1 :=
    normalization f 1
  have h2 : normalizedProfile f 2 = c * profile f 2 := by
    have h := normalization f 2
    change (1 : ℝ) * normalizedProfile f 2 = c * profile f 2 at h
    simpa only [_root_.one_mul] using h
  have h3 : (3 / 20 : ℝ) * normalizedProfile f 3 = c * profile f 3 :=
    normalization f 3
  have h4 : (1 / 80 : ℝ) * normalizedProfile f 4 = c * profile f 4 :=
    normalization f 4
  have he : ((5 : ℝ) * normalizedProfile f 1) ^ 2 +
      normalizedProfile f 2 ^ 2 + ((3 / 20 : ℝ) * normalizedProfile f 3) ^ 2 +
      ((1 / 80 : ℝ) * normalizedProfile f 4) ^ 2 =
      c ^ 2 * (∑ i : Fin 4, profile f i.succ ^ 2) := by
    rw [h1, h2, h3, h4]
    simp only [Fin.sum_univ_four,
      show (0 : Fin 4).succ = (1 : Fin 5) from rfl,
      show (1 : Fin 4).succ = (2 : Fin 5) from rfl,
      show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
      show (3 : Fin 4).succ = (4 : Fin 5) from rfl]
    ring
  unfold AESPaper.score
  rw [hA, he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  change c * (profile f 0 / 16384) +
    c * Real.sqrt (∑ i : Fin 4, profile f i.succ ^ 2) = _
  ring

end AESPaper.ProfileSpace
