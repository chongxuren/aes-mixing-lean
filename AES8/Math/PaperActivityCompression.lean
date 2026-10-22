import AES8.Math.PaperActivityExpansion
import AES8.Math.PaperTensorCompression

/-!
# Operator meaning of the outside activity expansion

The normalized nonzero factors are unit vectors. Their literal rank-one
projections compress to the activity slice, so its norm bound applies to
arbitrary full joint inputs without an independence assumption.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityCompression
open AESMixing WordActivityFrame PaperActivityExpansion PaperTensorCompression PaperKernelBounds
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {V I J X Y : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X] [DecidableEq X] [Fintype Y]

theorem nonzero_unit_energy (z : V) (hq : 1 < Fintype.card V) :
    (∑ x, nonzeroUnit z x ^ 2) = 1 := by
  have hp : 0 < q V - 1 := sub_pos.mpr (q_gt_one hq)
  have he (x : V) : nonzeroUnit z x ^ 2 =
      (1 - identityKernel x z) / (q V - 1) := by
    by_cases hx : x = z
    · simp [nonzeroUnit, identityKernel, hx]
    · simp [nonzeroUnit, identityKernel, hx, div_pow, Real.sq_sqrt hp.le]
  simp_rw [he]
  rw [← Finset.sum_div]
  have hs : (∑ x : V, (1 - identityKernel x z)) = q V - 1 := by
    simp [Finset.sum_sub_distrib, identityKernel, q]
  rw [hs, div_self hp.ne']

def activityUnit (z : V) (x : I → V) : ℝ := ∏ i, nonzeroUnit z (x i)

theorem activity_unit_energy (z : V) (hq : 1 < Fintype.card V) :
    (∑ x : I → V, activityUnit z x ^ 2) = 1 := by
  unfold activityUnit
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i x => nonzeroUnit z x ^ 2)]
  simp only [nonzero_unit_energy z hq, Finset.prod_const_one]

theorem compression_eq_slice (K : (Y × (I → V)) → (X × (J → V)) → ℝ) (z : V) :
    compressed K (activityUnit z) (activityUnit z) = nonzeroSlice K z := rfl

/-- The finite binomial bound controls the genuine activity-projected full
operator, with the actual projected input norm on the right. -/
theorem projected_norm_le_supportSum
    (K : (Y × (I → V)) → (X × (J → V)) → ℝ)
    (z : V) (hq : 1 < Fintype.card V) (G : ℕ → ℕ → ℝ)
    (hG : ∀ (s : Finset I) (t : Finset J),
      ‖kernelOperator (frameSlice K z s t)‖ ≤ G s.card t.card)
    (f : X × (J → V) → ℝ) :
    l2 (project (activityUnit z) (kernelAction K (project (activityUnit z) f))) ≤
      (Real.sqrt (eta V) ^ (Fintype.card I + Fintype.card J) *
        supportSum (Fintype.card I) (Fintype.card J) (xi V) G) *
          l2 (project (activityUnit z) f) := by
  apply projected_l2_le K (activityUnit z) (activityUnit z)
    (activity_unit_energy z hq) (activity_unit_energy z hq)
  rw [compression_eq_slice]
  exact norm_le_supportSum K z hq G hG

end AES8.PaperActivityCompression
