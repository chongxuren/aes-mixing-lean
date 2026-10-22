/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.ZeroOutsideProjection
import AES8.Reductions.Return.PhysicalZeroPattern

/-!
# Actual outside projections of the physical return summands

The output support-three projection absorbs the outer parallel channel into
three residual channels and a literal zero test. The input projection retains
its full signed joint residual coefficient. These are exact identities only;
no operator estimate or independence premise is introduced.
Constructive proofs only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace AES8.ProjectedReturn
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection
open AES8.PhysicalZeroPattern (channelTail frameReturnKernel fourReturnKernel)
open AES8.PhysicalMiddleKernel (channelFrameAtom)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def projectedChannel (D : V → V → ℝ) (r : Fin 4) :=
  coordinateKernel (fun i : Fin 4 =>
    if i = r then zeroMatrix (0 : V) else residualMatrix D 0)

theorem zeroMatrix_compose (D : V → V → ℝ) (hD : PointedBistochastic D 0) :
    kernelCompose (zeroMatrix (0 : V)) D = zeroMatrix 0 := by
  funext y x
  by_cases hy : y = 0 <;> by_cases hx : x = 0 <;>
    simp [kernelCompose, zeroMatrix, identityKernel, hD.zero_row, hy, hx]

theorem support_coordinates (r : Fin 4) :
    supportProduct (0 : V) (maskBit (outsideMask r)) (maskBit (singleMask r)) =
      coordinateKernel (fun i : Fin 4 =>
        if i = r then zeroMatrix (0 : V) else residualProjection 0) := by
  funext y x
  unfold supportProduct coordinateKernel
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = r
  · subst i
    have hm : maskBit (outsideMask r) r = false :=
      Bool.eq_false_iff.mpr (by simp [outsideMask_bit_iff])
    have hz : maskBit (singleMask r) r = true := (singleMask_bit_iff r r).mpr rfl
    simp [hm, hz, supportPiece]
  · have hm : maskBit (outsideMask r) i = true := (outsideMask_bit_iff r i).mpr hi
    have hz : maskBit (singleMask r) i = false :=
      Bool.eq_false_iff.mpr (fun h => hi ((singleMask_bit_iff r i).mp h))
    simp [hm, hz, hi, supportPiece]

theorem support_compose_parallel (D : V → V → ℝ)
    (hD : PointedBistochastic D 0) (r : Fin 4) :
    kernelCompose
      (supportProduct (0 : V) (maskBit (outsideMask r)) (maskBit (singleMask r)))
      (coordinateKernel (fun _ : Fin 4 => D)) = projectedChannel D r := by
  rw [support_coordinates, coordinateKernel_compose]
  unfold projectedChannel
  congr 1
  funext i
  by_cases hi : i = r
  · simp only [hi, if_true]
    exact zeroMatrix_compose D hD
  · simp only [hi, if_false]
    exact AESConcrete.FourResidualStep.pointed_residual_left D 0 hD

theorem Q_parallel (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    Q r (action (coordinateKernel (fun _ : Fin 4 => D)) f) =
      action (projectedChannel D r) f := by
  rw [Q_eq_support_action, ← kernelCompose_action, support_compose_parallel D hD]

/-- The output and the incoming outer-channel coordinate must both be zero. -/
theorem projectedChannel_entry (D : V → V → ℝ) (r : Fin 4)
    (y w : Fin 4 → V) :
    projectedChannel D r y w =
      if y r = 0 ∧ w r = 0 then channelTail D 0 r y w else 0 := by
  have h : projectedChannel D r y w =
      zeroMatrix 0 (y r) (w r) * channelTail D 0 r y w := by
    fin_cases r <;>
      simp [projectedChannel, channelTail, coordinateKernel, Fin.prod_univ_four] <;> ring
  rw [h]
  by_cases hy : y r = 0 <;> by_cases hw : w r = 0 <;>
    simp [zeroMatrix, identityKernel, hy, hw]

/-- Generic reindexing keeps the permutation opaque during finite sums. -/
theorem Q_relabel_integral (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : Equiv.Perm (Fin 4 → V)) (r : Fin 4) (h : (Fin 4 → V) → ℝ) :
    Q r (fun y => ∑ v, coordinateKernel (fun _ : Fin 4 => D) y (L v) * h v) =
      fun y => ∑ v, projectedChannel D r y (L v) * h v := by
  have he : (fun y => ∑ v, coordinateKernel (fun _ : Fin 4 => D) y (L v) * h v) =
      action (coordinateKernel (fun _ : Fin 4 => D)) (fun w => h (L.symm w)) := by
    funext y
    simpa only [L.symm_apply_apply, action] using Equiv.sum_comp L
      (fun w => coordinateKernel (fun _ : Fin 4 => D) y w * h (L.symm w))
  rw [he, Q_parallel D hD]
  funext y
  symm
  simpa only [L.symm_apply_apply, action] using Equiv.sum_comp L
    (fun w => projectedChannel D r y w * h (L.symm w))

end Generic

/-- Move the outside projection through the actual forward-boundary sum. -/
theorem Q_boundary_integral (r : Fin 4) (h : WordState → ℝ) :
    Q r (fun y => ∑ v, parallelSuperboxKernel y (wordMixAddEquiv v) * h v) =
      fun y => ∑ v, projectedChannel wordSuperboxKernel r y (wordMixAddEquiv v) * h v :=
  Q_relabel_integral wordSuperboxKernel word_superbox_pointed wordMixAddEquiv.toEquiv r h

theorem frame_action_integral (c : Fin 4) (s t : Bool) (f : WordState → ℝ) :
    action (frameReturnKernel c s t) f = fun y =>
      ∑ v, parallelSuperboxKernel y (wordMixAddEquiv v) *
        ∑ x, channelFrameAtom wordSuperboxKernel 0 c s t v (wordMixAddEquiv x) * f x := by
  funext y
  unfold action frameReturnKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem four_action_integral (f : WordState → ℝ) :
    action fourReturnKernel f = fun y =>
      ∑ v, parallelSuperboxKernel y (wordMixAddEquiv v) *
        ∑ x, AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x) * f x := by
  funext y
  unfold action fourReturnKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- All middle frame factors and the full signed input projection remain. -/
theorem projected_frame_integral (r c z : Fin 4) (s t : Bool) (f : WordState → ℝ) :
    Q r (action (frameReturnKernel c s t) (Q z f)) = fun y =>
      ∑ v, projectedChannel wordSuperboxKernel r y (wordMixAddEquiv v) *
        ∑ x, channelFrameAtom wordSuperboxKernel 0 c s t v (wordMixAddEquiv x) *
          Q z f x := by
  rw [frame_action_integral, Q_boundary_integral]

/-- The four-middle term has the same actual outside projection. -/
theorem projected_four_integral (r z : Fin 4) (f : WordState → ℝ) :
    Q r (action fourReturnKernel (Q z f)) = fun y =>
      ∑ v, projectedChannel wordSuperboxKernel r y (wordMixAddEquiv v) *
        ∑ x, AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x) *
          Q z f x := by
  rw [four_action_integral, Q_boundary_integral]

end AES8.ProjectedReturn
