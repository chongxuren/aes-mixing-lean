import AESMixing.FourTensor
import AESMixing.Gram

/-! Finite kernel algebra used for orthogonal activity/residual decompositions. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def identityKernel {V : Type*} [DecidableEq V] (y x : V) : ℝ := if y = x then 1 else 0

def kernelCompose {A B C : Type*} [Fintype B]
    (K : A → B → ℝ) (L : B → C → ℝ) (y : A) (x : C) : ℝ :=
  ∑ z, K y z * L z x

theorem identityKernel_action {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) : action identityKernel f = f := by
  funext y
  simp [action, identityKernel]

theorem kernelCompose_action {A B C : Type*} [Fintype B] [Fintype C]
    (K : A → B → ℝ) (L : B → C → ℝ) (f : C → ℝ) :
    action (kernelCompose K L) f = action K (action L f) := by
  funext y
  simp only [kernelCompose, action, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem kernel_action_ext {A B : Type*} [Fintype B] [DecidableEq B]
    (K L : A → B → ℝ) (h : ∀ f, action K f = action L f) : K = L := by
  funext y x
  have hh := congrFun (h (fun z => if z = x then 1 else 0)) y
  simpa [action] using hh

theorem kernel_action_add {A B : Type*} [Fintype B]
    (K L : A → B → ℝ) (f : B → ℝ) :
    action (K+L) f = action K f + action L f := by
  funext y
  simp [action, add_mul, Finset.sum_add_distrib]

theorem kernel_action_sub {A B : Type*} [Fintype B]
    (K L : A → B → ℝ) (f : B → ℝ) :
    action (K-L) f = action K f - action L f := by
  funext y
  simp [action, sub_mul, Finset.sum_sub_distrib]

theorem kernel_bilinear {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (K : A → B → ℝ) (L : A → C → ℝ) (f : B → ℝ) (g : C → ℝ) :
    (∑ y, action K f y * action L g y) =
      ∑ x, ∑ z, f x * g z * ∑ y, K y x * L y z := by
  have hex (y : A) : action K f y * action L g y =
      ∑ x, ∑ z, f x * g z * (K y x * L y z) := by
    unfold action
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  exact (Finset.mul_sum _ _ _).symm

theorem tensorKernel_compose {A B C D E F : Type*} [Fintype B] [Fintype E]
    (K : A → B → ℝ) (L : B → C → ℝ)
    (M : D → E → ℝ) (N : E → F → ℝ) :
    kernelCompose (tensorKernel K M) (tensorKernel L N) =
      tensorKernel (kernelCompose K L) (kernelCompose M N) := by
  funext y x
  simp only [kernelCompose, tensorKernel, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem activityMatrix_symmetric {V : Type*} [Fintype V] [DecidableEq V]
    (z x y : V) : activityMatrix z x y = activityMatrix z y x := by
  by_cases hx : x = z <;> by_cases hy : y = z <;> simp [activityMatrix, hx, hy]

theorem activityMatrix_idempotent {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) :
    kernelCompose (activityMatrix z) (activityMatrix z) = activityMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action, activityMatrix_action,
    wordAverage_idempotent z f hn]

def residualProjection {V : Type*} [Fintype V] [DecidableEq V] (z : V) : V → V → ℝ :=
  identityKernel - activityMatrix z

theorem residualProjection_action {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (f : V → ℝ) : action (residualProjection z) f = wordResidual z f := by
  rw [residualProjection, kernel_action_sub, identityKernel_action, activityMatrix_action]
  rfl

def degreePiece {V : Type*} [Fintype V] [DecidableEq V] (z : V) (b : Bool) : V → V → ℝ :=
  if b then residualProjection z else activityMatrix z

theorem degreePiece_symmetric {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (b : Bool) (x y : V) : degreePiece z b x y = degreePiece z b y x := by
  cases b
  · exact activityMatrix_symmetric z x y
  · change identityKernel x y - activityMatrix z x y =
      identityKernel y x - activityMatrix z y x
    rw [activityMatrix_symmetric z x y]
    simp only [identityKernel, eq_comm]

theorem degreePiece_sum {V : Type*} [Fintype V] [DecidableEq V]
    (z x y : V) : (∑ b : Bool, degreePiece z b x y) = identityKernel x y := by
  simp [degreePiece, residualProjection]

theorem degreePiece_compose {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (a b : Bool) :
    kernelCompose (degreePiece z a) (degreePiece z b) =
      if a = b then degreePiece z a else 0 := by
  apply kernel_action_ext
  intro f
  have hp := wordAverage_idempotent z f hn
  have hr : wordAverage z (wordResidual z f) = 0 := by
    rw [← activityMatrix_action z (wordResidual z f), wordResidual, action_sub,
      activityMatrix_action, activityMatrix_action, hp]
    exact sub_self _
  have hz : action (0 : V → V → ℝ) f = 0 := by
    funext x
    simp [action]
  cases a <;> cases b <;>
    simp only [degreePiece, Bool.false_eq_true, if_false, if_true,
      Bool.true_eq_false, kernelCompose_action, residualProjection_action,
      activityMatrix_action]
  · exact hp
  · rw [hr, hz]
  · rw [wordResidual, hp, sub_self, hz]
  · change wordResidual z f - wordAverage z (wordResidual z f) = wordResidual z f
    rw [hr, sub_zero]

end AESMixing
