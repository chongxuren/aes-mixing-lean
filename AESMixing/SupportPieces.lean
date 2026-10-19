import AESMixing.ResidualCoordinates

/-! Split the one-coordinate activity projection into its zero and
constant-nonzero directions. These are the orthogonal support pieces
used when assembling the residual diffusion blocks. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroPart (z : V) (f : V → ℝ) (x : V) : ℝ := if x = z then f z else 0

omit [Fintype V] in
theorem zeroPart_at_zero (z : V) (f : V → ℝ) : zeroPart z f z = f z := by simp [zeroPart]

theorem zeroPart_sum (z : V) (f : V → ℝ) : (∑ x, zeroPart z f x) = f z := by simp [zeroPart]

omit [Fintype V] in
theorem zeroPart_sub (z : V) (f g : V → ℝ) : zeroPart z (f-g) = zeroPart z f-zeroPart z g := by
  funext x
  by_cases hx : x = z <;> simp [zeroPart,hx]

omit [Fintype V] in
theorem zeroPart_idempotent (z : V) (f : V → ℝ) : zeroPart z (zeroPart z f) = zeroPart z f := by
  funext x
  simp [zeroPart]

omit [Fintype V] in
theorem zeroPart_zero (z : V) : zeroPart z (0 : V → ℝ) = 0 := by
  funext x
  simp [zeroPart]

theorem wordAverage_zeroPart (z : V) (f : V → ℝ) : wordAverage z (zeroPart z f) = zeroPart z f := by
  funext x
  simp [wordAverage,nonzeroMean,zeroPart]

theorem zeroPart_wordAverage (z : V) (f : V → ℝ) : zeroPart z (wordAverage z f) = zeroPart z f := by
  funext x
  simp [zeroPart,wordAverage_at_zero]

theorem wordAverage_sub (z : V) (f g : V → ℝ) :
    wordAverage z (f-g) = wordAverage z f-wordAverage z g := by
  simp_rw [← activityMatrix_action]
  exact action_sub (activityMatrix z) f g

theorem wordAverage_zero (z : V) : wordAverage z (0 : V → ℝ) = 0 := by
  funext x
  simp [wordAverage,nonzeroMean]

def zeroMatrix (z : V) (y x : V) : ℝ := identityKernel y z * identityKernel x z

theorem zeroMatrix_action (z : V) (f : V → ℝ) : action (zeroMatrix z) f = zeroPart z f := by
  funext y
  simp [action,zeroMatrix,identityKernel,zeroPart]

def constantMatrix (z : V) : V → V → ℝ := activityMatrix z-zeroMatrix z

theorem constantMatrix_action (z : V) (f : V → ℝ) :
    action (constantMatrix z) f = wordAverage z f-zeroPart z f := by
  rw [constantMatrix,kernel_action_sub,activityMatrix_action,zeroMatrix_action]

def supportPiece (z : V) (marked inactive : Bool) : V → V → ℝ :=
  if marked then (if inactive then 0 else residualProjection z)
  else if inactive then zeroMatrix z else constantMatrix z

omit [DecidableEq V] in
theorem zero_kernel_action (f : V → ℝ) : action (0 : V → V → ℝ) f = 0 := by
  funext x
  simp [action]

theorem supportPiece_symmetric (z : V) (marked inactive : Bool) (x y : V) :
    supportPiece z marked inactive x y = supportPiece z marked inactive y x := by
  cases marked <;> cases inactive <;> simp only [supportPiece,ite_true,Bool.false_eq_true,if_false]
  · simp only [constantMatrix,Pi.sub_apply,activityMatrix_symmetric z x y,zeroMatrix]
    ring
  · simp only [zeroMatrix]
    ring
  · exact degreePiece_symmetric z true x y
  · rfl

theorem supportPiece_sum (z : V) (marked : Bool) (x y : V) :
    (∑ inactive : Bool, supportPiece z marked inactive x y) = degreePiece z marked x y := by
  cases marked <;> simp [supportPiece,degreePiece,constantMatrix]

theorem supportPiece_compose (z : V) (hn : 1 < Fintype.card V)
    (marked a b : Bool) :
    kernelCompose (supportPiece z marked a) (supportPiece z marked b) =
      if a = b then supportPiece z marked a else 0 := by
  apply kernel_action_ext
  intro f
  cases marked <;> cases a <;> cases b <;>
    simp only [supportPiece,ite_true,Bool.false_eq_true,Bool.true_eq_false,if_false,
      kernelCompose_action,zero_kernel_action,constantMatrix_action,zeroMatrix_action,
      residualProjection_action,wordResidual,wordAverage_sub,zeroPart_sub,
      wordAverage_idempotent z f hn,wordAverage_zeroPart,zeroPart_wordAverage,
      zeroPart_idempotent,wordAverage_zero,sub_self,sub_zero]

end AESMixing
