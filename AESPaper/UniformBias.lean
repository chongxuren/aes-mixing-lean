import AESMixing.PointedProducts

/-!
# Uniform, centered activity bias, and residual projections

The full-uniform projection `J` is separated from the activity projection `P`.
The bias projection is `Z = P-J`, while the residual projection is `I-P`.
The three pieces are symmetric orthogonal idempotents and sum to the identity.
Left projection of a pointed bistochastic channel replaces the residual
projection by its residual matrix, leaving `J` and `Z` fixed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.UniformBias
open AESMixing

variable {V : Type*} [Fintype V]

/-- The uniform projection uses the entire finite space, including zero. -/
def uniformKernel : V → V → ℝ := fun _ _ => 1 / (Fintype.card V : ℝ)

theorem uniformKernel_symmetric (x y : V) : uniformKernel x y = uniformKernel y x := rfl

theorem uniformKernel_action (f : V → ℝ) :
    action uniformKernel f = fun _ => (∑ x, f x) / (Fintype.card V : ℝ) := by
  funext y
  change (∑ x, (1 / (Fintype.card V : ℝ)) * f x) =
    (∑ x, f x) / (Fintype.card V : ℝ)
  rw [← Finset.mul_sum]
  ring

theorem uniformKernel_idempotent (hn : 1 < Fintype.card V) :
    kernelCompose (uniformKernel : V → V → ℝ) uniformKernel = uniformKernel := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))
  funext y x
  simp only [kernelCompose, uniformKernel, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hc] <;> ring

theorem compose_sub_left (K L M : V → V → ℝ) :
    kernelCompose (K-L) M = kernelCompose K M - kernelCompose L M := by
  funext y x
  simp only [kernelCompose, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem compose_sub_right (K L M : V → V → ℝ) :
    kernelCompose K (L-M) = kernelCompose K L - kernelCompose K M := by
  funext y x
  simp only [kernelCompose, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

variable [DecidableEq V]

theorem identity_compose (K : V → V → ℝ) : kernelCompose identityKernel K = K := by
  funext y x
  simp [kernelCompose, identityKernel]

theorem compose_identity (K : V → V → ℝ) : kernelCompose K identityKernel = K := by
  funext y x
  simp [kernelCompose, identityKernel]

def biasKernel (z : V) : V → V → ℝ := activityMatrix z - uniformKernel

theorem biasKernel_action (z : V) (f : V → ℝ) :
    action (biasKernel z) f =
      wordAverage z f - (fun _ => (∑ x, f x) / (Fintype.card V : ℝ)) := by
  rw [biasKernel, kernel_action_sub, activityMatrix_action, uniformKernel_action]

/-- Indices zero, one, and two select `J`, `Z`, and `I-P`, respectively. -/
def piece (z : V) (a : Fin 3) : V → V → ℝ :=
  if a = 0 then uniformKernel else if a = 1 then biasKernel z else residualProjection z

/-- The same index selects the left-projected part of the channel. -/
def channelPiece (D : V → V → ℝ) (z : V) (a : Fin 3) : V → V → ℝ :=
  if a = 0 then uniformKernel else if a = 1 then biasKernel z else residualMatrix D z

theorem uniform_channel (D : V → V → ℝ) (z : V) (h : PointedBistochastic D z) :
    kernelCompose uniformKernel D = uniformKernel := by
  funext y x
  simp only [kernelCompose, uniformKernel, ← Finset.mul_sum, h.column_sum, mul_one]

theorem channel_uniform (D : V → V → ℝ) (z : V) (h : PointedBistochastic D z) :
    kernelCompose D uniformKernel = uniformKernel := by
  funext y x
  simp only [kernelCompose, uniformKernel, ← Finset.sum_mul, h.row_sum, one_mul]

theorem activity_channel (D : V → V → ℝ) (z : V) (h : PointedBistochastic D z) :
    kernelCompose (activityMatrix z) D = activityMatrix z := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action, activityMatrix_action, h.average_action, activityMatrix_action]

theorem uniform_activity (z : V) (hn : 1 < Fintype.card V) :
    kernelCompose uniformKernel (activityMatrix z) = uniformKernel :=
  uniform_channel _ z (activityMatrix_pointed z hn)

theorem activity_uniform (z : V) (hn : 1 < Fintype.card V) :
    kernelCompose (activityMatrix z) uniformKernel = uniformKernel :=
  channel_uniform _ z (activityMatrix_pointed z hn)

theorem piece_symmetric (z : V) (a : Fin 3) (x y : V) :
    piece z a x y = piece z a y x := by
  fin_cases a
  · rfl
  · change activityMatrix z x y - uniformKernel x y =
      activityMatrix z y x - uniformKernel y x
    rw [activityMatrix_symmetric z x y]
    rfl
  · exact degreePiece_symmetric z true x y

/-- Orthogonal idempotents for the full-uniform, bias, and residual pieces. -/
theorem piece_compose (z : V) (hn : 1 < Fintype.card V) (a b : Fin 3) :
    kernelCompose (piece z a) (piece z b) = if a = b then piece z a else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [piece, biasKernel, residualProjection, compose_sub_left, compose_sub_right,
      identity_compose, compose_identity, activityMatrix_idempotent z hn,
      uniform_activity z hn, activity_uniform z hn, uniformKernel_idempotent hn]

theorem piece_sum (z : V) : (∑ a : Fin 3, piece z a) = identityKernel := by
  funext x y
  simp [Fin.sum_univ_succ, piece, biasKernel, residualProjection] <;> ring

theorem piece_sum_apply (z x y : V) :
    (∑ a : Fin 3, piece z a x y) = identityKernel x y := by
  simpa only [Finset.sum_apply] using congrFun (congrFun (piece_sum z) x) y

theorem piece_channel (D : V → V → ℝ) (z : V) (h : PointedBistochastic D z)
    (a : Fin 3) : kernelCompose (piece z a) D = channelPiece D z a := by
  fin_cases a <;>
    simp [piece, channelPiece, biasKernel, residualProjection, compose_sub_left,
      identity_compose, activity_channel D z h, uniform_channel D z h] <;> rfl

theorem channelPiece_sum (D : V → V → ℝ) (z : V) :
    (∑ a : Fin 3, channelPiece D z a) = D := by
  funext x y
  simp [Fin.sum_univ_succ, channelPiece, biasKernel, residualMatrix] <;> ring

/-- The cross Gram kernels are the same orthogonal projections. -/
theorem piece_cross_gram (z : V) (hn : 1 < Fintype.card V) (a b : Fin 3) (x y : V) :
    (∑ t, piece z a t x * piece z b t y) =
      if a = b then piece z a x y else 0 := by
  calc
    _ = kernelCompose (piece z a) (piece z b) x y := by
      apply Finset.sum_congr rfl
      intro t _
      rw [piece_symmetric z a t x]
    _ = _ := by
      rw [piece_compose z hn a b]
      split_ifs <;> rfl

end AESPaper.UniformBias
