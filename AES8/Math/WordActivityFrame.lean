/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.ActivitySpan
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The shared activity frame over an arbitrary finite alphabet

For a distinguished value z and q = card V > 1, the normalized frame is
`[e_z, 1/sqrt(q)]`. Its Gram matrix has off-diagonal entry xi = 1/sqrt(q),
and its inverse is eta * [[1,-xi],[-xi,1]], with eta = q/(q-1).
The exact activity projection retains this shared inverse metric, including
both negative cross terms. Tensor reconstruction and action on arbitrary
signed joint functions follow by finite-sum identities.

This generic derivation does not apply the cardinal-256 byte theorem to
words. An AES-word specialization must use its actual cardinality separately.
No quantitative return cap, independence premise, attack, or manuscript or
predecessor edit is asserted. Compilation evidence is retained separately under evidence/.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

noncomputable section
open scoped BigOperators

namespace AES8.WordActivityFrame
open AESMixing

section ScalarFrame
variable (V : Type*) [Fintype V]

/-- The counting-measure alphabet cardinality, as a real scalar. -/
def q : ℝ := Fintype.card V

def xi : ℝ := 1 / Real.sqrt (q V)
def eta : ℝ := q V / (q V - 1)

def wordMetric (s t : Bool) : ℝ := if s = t then 1 else xi V

def wordInverse (s t : Bool) : ℝ :=
  eta V * if s = t then 1 else -(xi V)

variable {V}

theorem q_gt_one (hV : 1 < Fintype.card V) : 1 < q V := by
  change (1 : ℝ) < (Fintype.card V : ℝ)
  exact_mod_cast hV

theorem q_pos (hV : 1 < Fintype.card V) : 0 < q V :=
  lt_trans (by norm_num) (q_gt_one hV)

theorem q_ne_zero (hV : 1 < Fintype.card V) : q V ≠ 0 :=
  ne_of_gt (q_pos hV)

theorem q_sub_one_ne_zero (hV : 1 < Fintype.card V) : q V - 1 ≠ 0 :=
  ne_of_gt (sub_pos.mpr (q_gt_one hV))

theorem xi_sq (hV : 1 < Fintype.card V) : xi V ^ 2 = 1 / q V := by
  rw [xi, div_pow, one_pow, Real.sq_sqrt (q_pos hV).le]

theorem eta_mul_one_sub_xi_sq (hV : 1 < Fintype.card V) :
    eta V * (1 - xi V ^ 2) = 1 := by
  rw [xi_sq hV, eta]
  field_simp [q_ne_zero hV, q_sub_one_ne_zero hV] <;> ring

theorem eta_mul_xi_sq (hV : 1 < Fintype.card V) :
    eta V * xi V ^ 2 = 1 / (q V - 1) := by
  rw [xi_sq hV, eta]
  field_simp [q_ne_zero hV, q_sub_one_ne_zero hV] <;> ring

theorem wordMetric_symmetric (s t : Bool) : wordMetric V s t = wordMetric V t s := by
  simp [wordMetric, eq_comm]

theorem wordInverse_symmetric (s t : Bool) : wordInverse V s t = wordInverse V t s := by
  simp [wordInverse, eq_comm]

/-- Both metric cross terms are retained in the exact inverse calculation. -/
theorem word_inverse (hV : 1 < Fintype.card V) (s t : Bool) :
    (∑ u : Bool, wordMetric V s u * wordInverse V u t) = if s = t then 1 else 0 := by
  have h := eta_mul_one_sub_xi_sq hV
  cases s <;> cases t <;> simp [wordMetric, wordInverse] <;> nlinarith [h]

end ScalarFrame

section AlphabetFrame
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished value is explicit; no additive structure is required. -/
def wordFrame (z : V) (s : Bool) (x : V) : ℝ :=
  if s then xi V else identityKernel x z

theorem word_gram (z : V) (hV : 1 < Fintype.card V) (s t : Bool) :
    (∑ x : V, wordFrame z s x * wordFrame z t x) = wordMetric V s t := by
  cases s <;> cases t
  · simp [wordFrame, wordMetric, identityKernel]
  · simp [wordFrame, wordMetric, identityKernel]
  · simp [wordFrame, wordMetric, identityKernel]
  · change (∑ _x : V, xi V * xi V) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change q V * (xi V * xi V) = 1
    rw [← pow_two, xi_sq hV]
    field_simp [q_ne_zero hV]

/-- Exact reconstruction of the alphabet's activity kernel. This is proved
directly at arbitrary cardinality, rather than by a byte specialization. -/
theorem word_projection (z : V) (hV : 1 < Fintype.card V) (x y : V) :
    activityMatrix z x y =
      ∑ s : Bool, ∑ t : Bool,
        wordFrame z s x * wordInverse V s t * wordFrame z t y := by
  have hdiag := eta_mul_one_sub_xi_sq hV
  have hoff := eta_mul_xi_sq hV
  change eta V * xi V ^ 2 = 1 / ((Fintype.card V : ℝ) - 1) at hoff
  simp only [one_div] at hoff
  by_cases hx : x = z <;> by_cases hy : y = z <;>
    simp [wordFrame, wordInverse, activityMatrix, identityKernel, hx, hy] <;>
    nlinarith [hdiag, hoff]

/-- Exact action on a signed alphabet function, with the inverse metric used
once between the analysis and synthesis coefficients. -/
theorem word_projection_action (z : V) (hV : 1 < Fintype.card V) (f : V → ℝ) :
    action (activityMatrix z) f = fun x =>
      ∑ s : Bool, ∑ t : Bool,
        wordFrame z s x * wordInverse V s t * (∑ y : V, wordFrame z t y * f y) := by
  funext x
  unfold action
  simp_rw [word_projection z hV, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end AlphabetFrame

section TensorFrame
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def frameColumn (z : V) (s : I → Bool) (x : I → V) : ℝ := ∏ i, wordFrame z (s i) (x i)
def frameMetric (V : Type*) [Fintype V] (s t : I → Bool) : ℝ := ∏ i, wordMetric V (s i) (t i)
def frameInverse (V : Type*) [Fintype V] (s t : I → Bool) : ℝ := ∏ i, wordInverse V (s i) (t i)

theorem frame_gram (z : V) (hV : 1 < Fintype.card V) (s t : I → Bool) :
    (∑ x : I → V, frameColumn z s x * frameColumn z t x) = frameMetric V s t := by
  unfold frameColumn frameMetric
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => wordFrame z (s i) x * wordFrame z (t i) x)]
  simp_rw [word_gram z hV]

theorem frame_inverse (hV : 1 < Fintype.card V) (s t : I → Bool) :
    (∑ u : I → Bool, frameMetric V s u * frameInverse V u t) = if s = t then 1 else 0 := by
  unfold frameMetric frameInverse
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => wordMetric V (s i) u * wordInverse V u (t i))]
  simp_rw [word_inverse hV]
  rw [product_indicator]
  simp only [funext_iff]

/-- The shared activity projection over any finite coordinate family. -/
theorem frame_projection (z : V) (hV : 1 < Fintype.card V) (x y : I → V) :
    (∏ i, activityMatrix z (x i) (y i)) =
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameColumn z s x * frameInverse V s t * frameColumn z t y := by
  simp_rw [word_projection z hV]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [frameColumn, frameInverse, Finset.prod_mul_distrib]

/-- Full joint input is retained: no sign, product, or independence hypothesis
is used in this exact signed action identity. -/
theorem frame_projection_action (z : V) (hV : 1 < Fintype.card V)
    (f : (I → V) → ℝ) :
    action (coordinateKernel (fun _ : I => activityMatrix z)) f = fun x =>
      ∑ s : I → Bool, ∑ t : I → Bool,
        frameColumn z s x * frameInverse V s t *
          (∑ y : I → V, frameColumn z t y * f y) := by
  funext x
  change (∑ y : I → V, (∏ i, activityMatrix z (x i) (y i)) * f y) = _
  simp_rw [frame_projection z hV, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The coefficient norm is the full Gram quadratic, not an unweighted
sum of coefficient squares. -/
theorem frame_energy (z : V) (hV : 1 < Fintype.card V) (c : (I → Bool) → ℝ) :
    (∑ x : I → V, (∑ s : I → Bool, frameColumn z s x * c s)^2) =
      ∑ s : I → Bool, ∑ t : I → Bool, c s * c t * frameMetric V s t := by
  rw [gram_quadratic]
  simp only [gram, frame_gram z hV]

end TensorFrame

section FourCoordinateDegree
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The existing four-coordinate degree-zero kernel uses the generic frame. -/
theorem degree_zero_projection (z : V) (hV : 1 < Fintype.card V) (x y : Fin 4 → V) :
    degreeKernel z 0 x y =
      ∑ s : Fin 4 → Bool, ∑ t : Fin 4 → Bool,
        frameColumn z s x * frameInverse V s t * frameColumn z t y := by
  rw [degreeKernel_zero]
  change (∏ i, activityMatrix z (x i) (y i)) = _
  exact frame_projection z hV x y

/-- Exact degree-zero reconstruction for any signed four-coordinate input. -/
theorem degree_zero_action (z : V) (hV : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    degreeComponent z 0 f = fun x =>
      ∑ s : Fin 4 → Bool, ∑ t : Fin 4 → Bool,
        frameColumn z s x * frameInverse V s t *
          (∑ y : Fin 4 → V, frameColumn z t y * f y) := by
  rw [← degreeKernel_action, degreeKernel_zero]
  change action (coordinateKernel (fun _ : Fin 4 => activityMatrix z)) f = _
  exact frame_projection_action z hV f

end FourCoordinateDegree
end AES8.WordActivityFrame
