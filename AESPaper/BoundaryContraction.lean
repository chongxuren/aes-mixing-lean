import AESPaper.WordDamping
import AESPaper.BoundaryZeros
import AESPaper.Assembly

/-!
# Uniform boundary and high-degree contractions

The boundary transports a law by the inverse of the actual physical word
map. Its counting-measure Euclidean norm is unchanged on every signed input.
Combining that isometry with the already established word-degree damping
gives S34, S43 and S44, the raw entries Cij=1, and t4=1. These estimates do
not supply the other transfer entries or the complete uniform recurrence.

Editorial: retain the final boundary when identifying fourRound. The sandwich
below is H Pi H; fourRound is sandwich composed with the additional Pi.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.BoundaryContraction
open AESMixing AESConcrete
open AESPaper.ProfileSpace AESPaper.GroupedRecurrence
open AESPaper.WordDamping

/-- Actual law transport, including its inverse-map convention. -/
def boundaryLayer (f : ProfileSpace.State) : ProfileSpace.State :=
  WithLp.toLp 2 (Pi (fun x => f x))

theorem boundaryLayer_apply (f : ProfileSpace.State) (x : AES.WordState) :
    boundaryLayer f x = Pi (fun y => f y) x := rfl

/-- A permutation preserves counting energy without any sign restriction. -/
theorem boundaryLayer_norm (f : ProfileSpace.State) :
    ‖boundaryLayer f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [boundaryLayer_apply, Pi_apply]
  exact boundary.symm.toEquiv.sum_comp (fun x => f x ^ 2)

theorem boundaryLayer_centered (f : ProfileSpace.State) (hf : Centered f) :
    Centered (boundaryLayer f) := by
  constructor
  · rw [boundaryLayer_apply, Pi_apply, map_zero]
    exact hf.1
  · have hs : (∑ x, f (boundary.symm x)) = ∑ x, f x :=
      boundary.symm.toEquiv.sum_comp (fun x => f x)
    simpa only [boundaryLayer_apply, Pi_apply] using hs.trans hf.2

theorem component_apply_norm_le (i : Fin 5) (f : ProfileSpace.State) :
    ‖component i f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖component i‖ * ‖f‖ := (component i).le_opNorm f
    _ ≤ 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right (component_norm_le i) (norm_nonneg f)
    _ = _ := one_mul _

/-- The paper's two-layer sandwich D4; it omits the separate right boundary. -/
def sandwich (f : ProfileSpace.State) : ProfileSpace.State :=
  layer (boundaryLayer (layer f))

theorem sandwich_apply (f : ProfileSpace.State) (x : AES.WordState) :
    sandwich f x = H (Pi (H (fun y => f y))) x := by
  -- Typed congruences keep kernel checking from unfolding the concrete AES
  -- state and parallel kernel while identifying the nested function arguments.
  have hs : sandwich f x = layer (boundaryLayer (layer f)) x := rfl
  have hb : (fun y => boundaryLayer (layer f) y) = Pi (fun y => layer f y) :=
    funext (fun y => boundaryLayer_apply (layer f) y)
  have hh : (fun y => layer f y) = H (fun y => f y) :=
    funext (fun y => layer_apply f y)
  exact hs.trans ((layer_apply (boundaryLayer (layer f)) x).trans
    ((congrArg (fun g : AES.WordState → ℝ => H g x) hb).trans
      (congrArg (fun g : AES.WordState → ℝ => H (Pi g) x) hh)))

/-- The repeated operator keeps the final Pi, even in this wrapper. -/
theorem fourRound_eq_sandwich_boundary (f : ProfileSpace.State) :
    ConcreteProfile.fourRound f = sandwich (boundaryLayer f) := by
  apply PiLp.ext
  intro x
  have hr : ConcreteProfile.fourRound f x =
      H (Pi (H (Pi (fun y => f y)))) x :=
    PiLp.toLp_apply 2 (fun _ : AES.WordState => ℝ)
      (H (Pi (H (Pi (fun y => f y))))) x
  have hb : (fun y => boundaryLayer f y) = Pi (fun y => f y) :=
    funext (fun y => boundaryLayer_apply f y)
  have he := congrArg (fun g : AES.WordState → ℝ => H (Pi (H g)) x) hb
  exact hr.trans ((sandwich_apply (boundaryLayer f) x).trans he).symm

/-- Every raw projected boundary block has norm at most one on arbitrary f. -/
theorem raw_component_norm (i j : Fin 5) (f : ProfileSpace.State) :
    ‖component i (boundaryLayer (component j f))‖ ≤ ‖component j f‖ := by
  calc
    _ ≤ ‖boundaryLayer (component j f)‖ := component_apply_norm_le i _
    _ = _ := boundaryLayer_norm _

/-- Both word layers damp, with no product-law or centering hypothesis. -/
theorem sandwich_component_norm (i j : Fin 5) (f : ProfileSpace.State) :
    ‖component i (sandwich (component j f))‖ ≤
      nu ^ (i.val + j.val) * ‖component j f‖ := by
  change ‖component i (layer (boundaryLayer (layer (component j f))))‖ ≤ _
  rw [← layer_component]
  calc
    _ ≤ nu ^ i.val * ‖component i (boundaryLayer (layer (component j f)))‖ :=
      layer_component_norm i _
    _ ≤ nu ^ i.val * ‖boundaryLayer (layer (component j f))‖ :=
      mul_le_mul_of_nonneg_left (component_apply_norm_le i _)
        (pow_nonneg nu_nonnegative _)
    _ = nu ^ i.val * ‖layer (component j f)‖ := by rw [boundaryLayer_norm]
    _ ≤ nu ^ i.val * (nu ^ j.val * ‖component j f‖) :=
      mul_le_mul_of_nonneg_left (layer_component_norm j f)
        (pow_nonneg nu_nonnegative _)
    _ = _ := by rw [pow_add]; ring

/-- The raw table has unit caps precisely in the upper degree region. -/
theorem C_eq_one_of_large_degree (i j : Fin 4) (hij : 3 ≤ i.val + j.val) :
    Assembly.C i j = 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Assembly.C, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at *

theorem raw_C_unit (i j : Fin 4) (hij : 3 ≤ i.val + j.val)
    (f : ProfileSpace.State) :
    ‖component i.succ (boundaryLayer (component j.succ f))‖ ≤
      Assembly.C i j * ‖component j.succ f‖ := by
  rw [C_eq_one_of_large_degree i j hij, one_mul]
  exact raw_component_norm i.succ j.succ f

/-- The t4 boundary-to-activity cap is one, including for arbitrary signs. -/
theorem raw_activity_four (f : ProfileSpace.State) :
    ‖component 0 (boundaryLayer (component 4 f))‖ ≤
      Assembly.t 3 * ‖component 4 f‖ := by
  have ht : Assembly.t 3 = 1 := by norm_num [Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rw [ht, one_mul]
  exact raw_component_norm 0 4 f

theorem raw_four_activity (f : ProfileSpace.State) :
    ‖component 4 (boundaryLayer (component 0 f))‖ ≤
      Assembly.t 3 * ‖component 0 f‖ := by
  have ht : Assembly.t 3 = 1 := by norm_num [Assembly.t, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rw [ht, one_mul]
  exact raw_component_norm 4 0 f

/-- Exact rational rounding of the generic damping at degrees 3 <- 4. -/
theorem sandwich_S34 (f : ProfileSpace.State) :
    ‖component 3 (sandwich (component 4 f))‖ ≤
      (Assembly.S 2 3 / Assembly.q ^ 2) * ‖component 4 f‖ := by
  have hc : nu ^ ((3 : Fin 5).val + (4 : Fin 5).val) ≤
      Assembly.S 2 3 / Assembly.q ^ 2 := by
    norm_num [nu, Assembly.S, Assembly.q, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  exact (sandwich_component_norm 3 4 f).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem sandwich_S43 (f : ProfileSpace.State) :
    ‖component 4 (sandwich (component 3 f))‖ ≤
      (Assembly.S 3 2 / Assembly.q ^ 2) * ‖component 3 f‖ := by
  have hc : nu ^ ((4 : Fin 5).val + (3 : Fin 5).val) ≤
      Assembly.S 3 2 / Assembly.q ^ 2 := by
    norm_num [nu, Assembly.S, Assembly.q, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  exact (sandwich_component_norm 4 3 f).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem sandwich_S44 (f : ProfileSpace.State) :
    ‖component 4 (sandwich (component 4 f))‖ ≤
      (Assembly.S 3 3 / Assembly.q ^ 2) * ‖component 4 f‖ := by
  have hc : nu ^ ((4 : Fin 5).val + (4 : Fin 5).val) ≤
      Assembly.S 3 3 / Assembly.q ^ 2 := by
    norm_num [nu, Assembly.S, Assembly.q, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  exact (sandwich_component_norm 4 4 f).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end AESPaper.BoundaryContraction
