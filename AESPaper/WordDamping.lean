import AESPaper.Profile
import AESPaper.ConcreteProfile
import AESConcrete.WordChannelCommutation
import AESConcrete.SharpDampedWordNorm

/-!
WordDamping: auxiliary lemmas for the concrete AES mixing proof.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordDamping
open AESMixing AESConcrete AESPaper.ProfileSpace
open AESConcrete.WordChannelCommutation

def nu : ℝ := 21 / 131072

theorem nu_nonnegative : 0 ≤ nu := by norm_num [nu]

def wordPiece (b : Bool) : AES.Word → AES.Word → ℝ :=
  if b then residualMatrix AES.wordSuperboxKernel 0 else activityMatrix 0

def pieceBound (b : Bool) : ℝ := if b then nu else 1

theorem wordPiece_energy (b : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (wordPiece b) f y ^ 2) ≤ pieceBound b ^ 2 * ∑ x, f x ^ 2 := by
  cases b
  · simp only [wordPiece, pieceBound, Bool.false_eq_true, if_false, one_pow,
      _root_.one_mul, activityMatrix_action]
    have he := activity_residual_pythagoras (0 : AES.Word) f word_card_gt_one
    have hp : 0 ≤ ∑ x, wordResidual (0 : AES.Word) f x ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  · exact SharpDampedWordNorm.word_superbox_residual_energy f

theorem word_degree_right (b : Bool) :
    kernelCompose AES.wordSuperboxKernel (degreePiece (0 : AES.Word) b) =
      wordPiece b := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  cases b
  · change action AES.wordSuperboxKernel (action (activityMatrix 0) f) =
      action (activityMatrix 0) f
    rw [activityMatrix_action, AES.word_superbox_pointed.action_average]
  · change action AES.wordSuperboxKernel (action (residualProjection 0) f) =
      action (residualMatrix AES.wordSuperboxKernel 0) f
    rw [residualProjection_action, residualMatrix_action AES.word_superbox_pointed]

theorem pieceBound_product (a : Fin 4 → Bool) :
    (∏ i, pieceBound (a i)) = nu ^ residualDegree a := by
  simp [pieceBound, residualDegree, Finset.prod_ite]

theorem parallel_pattern_right (a : Fin 4 → Bool) :
    kernelCompose AES.parallelSuperboxKernel (productProjection (0 : AES.Word) a) =
      coordinateKernel (fun i => wordPiece (a i)) := by
  change kernelCompose (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel))
    (coordinateKernel (fun i => degreePiece (0 : AES.Word) (a i))) = _
  rw [coordinateKernel_compose]
  simp_rw [word_degree_right]

theorem parallel_pattern_commutes (a : Fin 4 → Bool) (f : AES.WordState → ℝ) :
    action (productProjection (0 : AES.Word) a) (action AES.parallelSuperboxKernel f) =
      action AES.parallelSuperboxKernel (action (productProjection (0 : AES.Word) a) f) := by
  rw [← kernelCompose_action, ← kernelCompose_action]
  exact congrArg (fun K => action K f)
    (coordinate_pattern_commutes (fun _ : Fin 4 => AES.word_superbox_pointed) a).symm

theorem parallel_pattern_energy (a : Fin 4 → Bool) (f : AES.WordState → ℝ) :
    (∑ y, action AES.parallelSuperboxKernel
      (action (productProjection (0 : AES.Word) a) f) y ^ 2) ≤
      (nu ^ residualDegree a) ^ 2 *
        ∑ x, action (productProjection (0 : AES.Word) a) f x ^ 2 := by
  let g := action (productProjection (0 : AES.Word) a) f
  have hproj : action (productProjection (0 : AES.Word) a) g = g := by
    change action (productProjection (0 : AES.Word) a)
      (action (productProjection (0 : AES.Word) a) f) = _
    rw [← kernelCompose_action, productProjection_compose 0 word_card_gt_one]
    simp only [if_true]
    rfl
  have he := four_coordinate_energy (fun i => wordPiece (a i))
    (fun i => pieceBound (a i)) (fun i => wordPiece_energy (a i)) g
  rw [pieceBound_product, ← parallel_pattern_right, kernelCompose_action, hproj] at he
  exact he

/-- Degree counts residual 32-bit words. No independence assumption on f. -/
theorem parallel_degree_energy (j : Fin 5) (f : AES.WordState → ℝ) :
    (∑ y, action AES.parallelSuperboxKernel (degreeComponent (0 : AES.Word) j f) y ^ 2) ≤
      (nu ^ j.val) ^ 2 * ∑ x, degreeComponent (0 : AES.Word) j f x ^ 2 := by
  rw [parallel_word_degree_commutes, degreeComponent_energy 0 word_card_gt_one,
    degreeComponent_energy 0 word_card_gt_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : degreeIndex a = j
  · simp only [ha, if_true]
    have hd : residualDegree a = j.val := congrArg Fin.val ha
    simpa only [← parallel_pattern_commutes a f, hd] using parallel_pattern_energy a f
  · simp only [ha, if_false, mul_zero]
    exact le_rfl

/-- Continuous linear map for the actual four parallel word superboxes. -/
def layer : ProfileSpace.State →L[ℝ] ProfileSpace.State :=
  kernelOperator AES.parallelSuperboxKernel

theorem layer_apply (f : ProfileSpace.State) (x : AES.WordState) :
    layer f x = GroupedRecurrence.H (fun y => f y) x :=
  kernelOperator_apply _ f x

theorem layer_component (i : Fin 5) (f : ProfileSpace.State) :
    layer (component i f) = component i (layer f) := by
  ext x
  simp only [layer_apply, component_apply, GroupedRecurrence.H]
  exact congrFun (parallel_word_degree_commutes i (fun y => f y)) x

theorem activity_layer (f : ProfileSpace.State) :
    component 0 (layer f) = component 0 f := by
  ext x
  simp only [component_apply, layer_apply, GroupedRecurrence.H]
  exact congrFun (parallel_word_activity_left (fun y => f y)) x

theorem layer_activity (f : ProfileSpace.State) :
    layer (component 0 f) = component 0 f := by
  rw [layer_component, activity_layer]

theorem layer_component_norm (i : Fin 5) (f : ProfileSpace.State) :
    ‖layer (component i f)‖ ≤ nu ^ i.val * ‖component i f‖ := by
  have h := l2_le_of_energy _ _ (nu ^ i.val) (pow_nonneg nu_nonnegative _)
    (parallel_degree_energy i (fun x => f x))
  have hout : (fun x => layer (component i f) x) =
      action AES.parallelSuperboxKernel (degreeComponent (0 : AES.Word) i (fun x => f x)) := by
    funext x
    simp only [layer_apply, component_apply, GroupedRecurrence.H]
  have hin : (fun x => component i f x) =
      degreeComponent (0 : AES.Word) i (fun x => f x) := by
    funext x
    exact component_apply i f x
  rw [← hout, ← hin, l2_eq_norm, l2_eq_norm] at h
  exact h

theorem profile_layer (f : ProfileSpace.State) (i : Fin 5) :
    profile (layer f) i ≤ nu ^ i.val * profile f i := by
  unfold profile
  rw [← layer_component]
  exact layer_component_norm i f

theorem layer_centered (f : ProfileSpace.State) (hf : Centered f) :
    Centered (layer f) := by
  have hp : PointedBistochastic AES.parallelSuperboxKernel (0 : AES.WordState) :=
    coordinateKernel_pointed _ _ (fun _ => AES.word_superbox_pointed)
  constructor
  · rw [layer_apply]
    exact (hp.action_zero (fun x => f x)).trans hf.1
  · simp only [layer_apply, GroupedRecurrence.H]
    exact (hp.action_sum (fun x => f x)).trans hf.2

theorem layer_norm_le (f : ProfileSpace.State) : ‖layer f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← profile_energy, ← profile_energy]
  apply Finset.sum_le_sum
  intro i _
  have hn : nu ^ i.val ≤ 1 := pow_le_one₀ nu_nonnegative (by norm_num [nu])
  have h := (profile_layer f i).trans
    (mul_le_of_le_one_left (profile_nonnegative f i) hn)
  exact (sq_le_sq₀ (profile_nonnegative _ _) (profile_nonnegative _ _)).mpr h

end AESPaper.WordDamping
