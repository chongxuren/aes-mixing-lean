import AES8.Math.PaperActivityCompression
import AES8.Reductions.Support.PaperSupportProjectionLaws
import Mathlib.Logic.Equiv.Prod

/-!
# Literal coordinates of a fixed support projection

Residual coordinates and outside coordinates retain their physical labels.
The support tensor splits into its residual kernel and a unit outside factor,
including the prescribed zero coordinates.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportCoordinates
open AESMixing PaperSupportProjection WordActivityFrame PaperActivityExpansion
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

abbrev Residual (p : Label n) := {k : Fin n // p.1 k = true}
abbrev Outside (p : Label n) := {k : Fin n // ¬p.1 k = true}

def split (p : Label n) : (Fin n → V) ≃ (Residual p → V) × (Outside p → V) :=
  Equiv.piEquivPiSubtypeProd (fun k => p.1 k = true) (fun _ => V)

def outsideUnit (z : V) (p : Label n) (x : Outside p → V) : ℝ :=
  ∏ k, if p.2 k.val then wordFrame z false (x k) else nonzeroUnit z (x k)

def residualKernel (z : V) (p : Label n) (y x : Residual p → V) : ℝ :=
  ∏ k, residualProjection z (y k) (x k)

theorem constantMatrix_unit (z : V) (hq : 1 < Fintype.card V) (y x : V) :
    constantMatrix z y x = nonzeroUnit z y * nonzeroUnit z x := by
  have hp : 0 < q V - 1 := sub_pos.mpr (q_gt_one hq)
  by_cases hy : y = z <;> by_cases hx : x = z <;>
    simp [constantMatrix, activityMatrix, zeroMatrix, identityKernel, nonzeroUnit, hy, hx]
  rw [← mul_inv, ← pow_two, Real.sq_sqrt hp.le]
  rfl

theorem outside_unit_energy (z : V) (hq : 1 < Fintype.card V) (p : Label n) :
    (∑ x : Outside p → V, outsideUnit z p x ^ 2) = 1 := by
  unfold outsideUnit
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (k : Outside p) (v : V) =>
    (if p.2 k.val then wordFrame z false v else nonzeroUnit z v)^2)]
  have h (k : Outside p) :
      (∑ v : V, (if p.2 k.val then wordFrame z false v else nonzeroUnit z v)^2) = 1 := by
    cases hs : p.2 k.val
    · simpa only [hs, Bool.false_eq_true, if_false] using
        PaperActivityCompression.nonzero_unit_energy z hq
    · simp [hs, wordFrame, identityKernel]
  simp only [h, Finset.prod_const_one]

/-- Exact tensor factorization; no discarded support or normalization factor. -/
theorem raw_kernel_split (z : V) (hq : 1 < Fintype.card V)
    (p : Label n) (hp : Valid p) (y x : Fin n → V) :
    supportProduct z p.1 p.2 y x =
      residualKernel z p ((split p) y).1 ((split p) x).1 *
      outsideUnit z p ((split p) y).2 * outsideUnit z p ((split p) x).2 := by
  unfold supportProduct
  rw [← Finset.prod_filter_mul_prod_filter_not (p := fun k => p.1 k = true)]
  have hres : (∏ k ∈ Finset.univ.filter (fun k => p.1 k = true),
      supportPiece z (p.1 k) (p.2 k) (y k) (x k)) =
      residualKernel z p ((split p) y).1 ((split p) x).1 := by
    change _ = ∏ k : Residual p, residualProjection z (y k.val) (x k.val)
    rw [← Finset.prod_subtype (p := fun k => p.1 k = true)
      (Finset.univ.filter (fun k => p.1 k = true)) (by simp)
      (fun k => residualProjection z (y k) (x k))]
    apply Finset.prod_congr rfl
    intro k hk
    have hm := (Finset.mem_filter.mp hk).2
    simp [supportPiece, hm, hp k hm, split]
  have hout : (∏ k ∈ Finset.univ.filter (fun k => ¬p.1 k = true),
      supportPiece z (p.1 k) (p.2 k) (y k) (x k)) =
      outsideUnit z p ((split p) y).2 * outsideUnit z p ((split p) x).2 := by
    unfold outsideUnit
    rw [← Finset.prod_mul_distrib]
    change _ = ∏ k : Outside p,
      (if p.2 k.val then wordFrame z false (y k.val) else nonzeroUnit z (y k.val)) *
      (if p.2 k.val then wordFrame z false (x k.val) else nonzeroUnit z (x k.val))
    rw [← Finset.prod_subtype (p := fun k => ¬p.1 k = true)
      (Finset.univ.filter (fun k => ¬p.1 k = true)) (by simp)
      (fun k => (if p.2 k then wordFrame z false (y k) else nonzeroUnit z (y k)) *
        (if p.2 k then wordFrame z false (x k) else nonzeroUnit z (x k)))]
    apply Finset.prod_congr rfl
    intro k hk
    have hm : p.1 k = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hk).2
    cases hs : p.2 k
    · simpa only [supportPiece, hm, hs, Bool.false_eq_true, if_false] using
        constantMatrix_unit z hq (y k) (x k)
    · simp [supportPiece, hm, hs, zeroMatrix, wordFrame, split]
  rw [hres, hout]
  ring

/-- The remaining coordinates carry the genuine all-residual projection. -/
theorem residualKernel_eq (z : V) (p : Label n) :
    residualKernel z p = productProjection z (fun _ : Residual p => true) := by
  funext y x
  simp only [residualKernel, productProjection, degreePiece, if_true]

theorem residual_idempotent (z : V) (hq : 1 < Fintype.card V) (p : Label n)
    (f : (Residual p → V) → ℝ) :
    action (residualKernel z p) (action (residualKernel z p) f) =
      action (residualKernel z p) f := by
  rw [← kernelCompose_action, residualKernel_eq, productProjection_compose z hq]
  simp

/-- Exact action after the physical residual/outside coordinate split. -/
theorem raw_action_split (z : V) (hq : 1 < Fintype.card V)
    (p : Label n) (hp : Valid p) (f : (Fin n → V) → ℝ) :
    (fun y => raw z p f ((split p).symm y)) =
      PaperTensorCompression.embed (outsideUnit z p)
        (action (residualKernel z p)
          (PaperTensorCompression.collapse (outsideUnit z p) (fun x => f ((split p).symm x)))) := by
  funext y
  unfold raw action
  rw [← (split p).symm.sum_comp]
  simp only [raw_kernel_split z hq p hp, Equiv.apply_symm_apply, Fintype.sum_prod_type]
  unfold PaperTensorCompression.embed PaperTensorCompression.collapse
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  ring

end AES8.PaperSupportCoordinates
