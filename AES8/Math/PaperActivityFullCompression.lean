import AES8.Math.PaperActivityCenteredNorm

/-! The all-zero state bookkeeping for the full printed activity operator.
The all-zero diffusion block cancels its fixed projection, and the remaining
uniform-nonzero sandwiches sum to the literal global uniform projection. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperActivityFullCompression
open AESMixing AESConcrete.RefinedWordProjection
open AESConcrete.ActivityRankOneStep (activityIndicator)
open AESConcrete.RefinedProjectionCompleteness
open AESConcrete.DegreeCentering (distinguishedState globalUniformKernel)
open PaperKernelBounds PaperActivityOperatorCompression PaperActivityCenteredNorm
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

private theorem weight_eq_succ (a : Fin 4) : weight a = a.succ := rfl

private theorem sum_five (f : Fin 5 → ℝ) :
    (∑ a : Fin 5, f a) = f 0 + ∑ a : Fin 4, f (weight a) := by
  simpa only [weight_eq_succ] using Fin.sum_univ_succ f

/-- The activity class of size zero is the actual distinguished-state indicator. -/
theorem indicator_zero (y : Fin 4 → V) : activityIndicator (0 : Fin 5) y =
    if y = distinguishedState (0 : V) then 1 else 0 := by
  simp [activityIndicator, action, refined_zero_zero, zeroMatrix, identityKernel]

/-- The four nonzero classes partition precisely the complement of the zero state. -/
theorem nonzero_indicator_sum (hn : 1 < Fintype.card V) (y : Fin 4 → V) :
    (∑ a : Fin 4, activityIndicator (weight a) y) =
      if y = distinguishedState (0 : V) then 0 else 1 := by
  have hall : (∑ a : Fin 5, activityIndicator a y) = 1 := by
    simp only [activityIndicator, action, mul_one]
    rw [Finset.sum_comm]
    have hh (x : Fin 4 → V) : (∑ a : Fin 5, refinedKernel (0 : V) 0 a y x) =
        degreeKernel (0 : V) 0 y x :=
      congrFun (congrFun (refined_sum_active (0 : V) 0) y) x
    simp_rw [hh]
    exact (degree_zero_pointed (0 : V) hn).row_sum y
  rw [Fin.sum_univ_succ] at hall
  simp only [← weight_eq_succ] at hall
  rw [indicator_zero] at hall
  split_ifs at hall ⊢ <;> linarith

private def blockKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) (a b : Fin 5) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (fun y z => refinedKernel (0 : V) 0 a y (L z))
    (refinedKernel (0 : V) 0 b)

private theorem zero_left (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a : Fin 4) :
    blockKernel L 0 (weight a) = 0 := by
  rw [blockKernel, AESConcrete.ActivityFullStep.diffusion_activity_rank_one hn L hL]
  have hz : weight a ≠ 0 := weight_ne_zero a
  funext y x
  simp [AESConcrete.ActivityMDSCounts.supportCount_small _ (weight a) hz]

private theorem zero_right (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a : Fin 4) :
    blockKernel L (weight a) 0 = 0 := by
  rw [blockKernel, AESConcrete.ActivityFullStep.diffusion_activity_rank_one hn L hL]
  have hz : weight a ≠ 0 := weight_ne_zero a
  funext y x
  simp [AESConcrete.ActivityMDSCounts.supportCount_small _ (weight a) hz]

private theorem zero_zero (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    blockKernel L 0 0 = zeroMatrix (distinguishedState (0 : V)) := by
  rw [blockKernel, AESConcrete.ActivityFullStep.diffusion_activity_rank_one hn L hL]
  funext y x
  have hc0 : AESConcrete.ActivityMDSCounts.supportCount (Fintype.card V) 0 = 1 := by
    simp [AESConcrete.ActivityMDSCounts.supportCount]
  simp only [Fin.val_zero, Nat.add_zero, pow_zero, hc0, div_one, one_mul, indicator_zero]
  by_cases hy : y = distinguishedState (0 : V) <;>
    by_cases hx : x = distinguishedState (0 : V) <;>
    simp [zeroMatrix, identityKernel, hy, hx]

private theorem compose_finite_sums {I J : Type*} [Fintype I] [Fintype J]
    (K : I → (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (H : J → (Fin 4 → V) → (Fin 4 → V) → ℝ) (y x : Fin 4 → V) :
    kernelCompose (fun y z => ∑ i, K i y z) (fun z x => ∑ j, H j z x) y x =
      ∑ i, ∑ j, kernelCompose (K i) (H j) y x := by
  simpa only [kernelCompose] using
    AESMixing.sum_family_inner (fun z i => K i y z) (fun z j => H j z x)

/-- Before centering, the full activity sandwich has one additional zero block. -/
theorem full_raw_split (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    kernelCompose (fun y z => degreeKernel (0 : V) 0 y (L z)) (degreeKernel 0 0) =
      zeroMatrix (distinguishedState (0 : V)) + actualKernel L := by
  funext y x
  have hp : degreeKernel (0 : V) 0 =
      fun y x => ∑ a : Fin 5, refinedKernel (0 : V) 0 a y x :=
    (refined_sum_active (0 : V) 0).symm
  rw [hp]
  rw [compose_finite_sums]
  change (∑ a : Fin 5, ∑ b : Fin 5, blockKernel L a b y x) = _
  rw [sum_five]
  simp only [sum_five]
  simp only [zero_left hn L hL, zero_right hn L hL, zero_zero hn L hL,
    Pi.zero_apply, Finset.sum_const_zero, zero_add, add_zero, Pi.add_apply]
  rfl

/-- The uniform-nonzero projection is exactly the sum of its genuine four-by-four
activity sandwiches. -/
theorem uniform_sum (hn : 1 < Fintype.card V) (y x : Fin 4 → V) :
    (∑ a : Fin 4, ∑ b : Fin 4,
      kernelCompose (refinedKernel (0 : V) 0 (weight a))
        (kernelCompose (globalUniformKernel 0)
          (refinedKernel (0 : V) 0 (weight b))) y x) = globalUniformKernel 0 y x := by
  have hterm (a b : Fin 4) := AESConcrete.ActivityRankOneStep.uniform_sandwich
    (V := V) (weight a) (weight b)
    (weight_ne_zero a) (weight_ne_zero b) y x
  simp_rw [hterm]
  have he : (∑ a : Fin 4, ∑ b : Fin 4,
      activityIndicator (weight a) y * activityIndicator (weight b) x /
        ((Fintype.card V : ℝ)^4-1)) =
      (∑ a : Fin 4, activityIndicator (weight a) y) *
        (∑ b : Fin 4, activityIndicator (weight b) x) /
          ((Fintype.card V : ℝ)^4-1) := by
    simp only [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [he, nonzero_indicator_sum hn y, nonzero_indicator_sum hn x]
  by_cases hy : y = distinguishedState (0 : V) <;>
    by_cases hx : x = distinguishedState (0 : V) <;>
    simp [globalUniformKernel, hy, hx, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- Literal full operator P_activity U_L P_activity - P_fixed. -/
def fullCenteredKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (fun y z => degreeKernel (0 : V) 0 y (L z)) (degreeKernel 0 0) -
    (zeroMatrix (distinguishedState (0 : V)) + globalUniformKernel 0)

theorem full_centered_eq (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    fullCenteredKernel L = centeredKernel L := by
  rw [fullCenteredKernel, full_raw_split hn L hL]
  funext y x
  simp only [centeredKernel, Finset.sum_sub_distrib, Pi.sub_apply, Pi.add_apply]
  rw [uniform_sum hn]
  change _ = actualKernel L y x - _
  ring

theorem full_activity_norm (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    ‖kernelOperator (fullCenteredKernel L)‖ =
      (5*((Fintype.card V : ℝ)+1)+Real.sqrt
        ((Fintype.card V : ℝ)^2+98*(Fintype.card V : ℝ)+1))/
          ((Fintype.card V : ℝ)-1)^3 := by
  rw [full_centered_eq hn L hL]
  exact actual_activity_norm hn L hL

theorem full_activity_hs (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    (∑ y : Fin 4 → V, ∑ x : Fin 4 → V, fullCenteredKernel L y x ^ 2) =
      (68*(Fintype.card V : ℝ)^2+264*(Fintype.card V : ℝ)+68)/
        ((Fintype.card V : ℝ)-1)^6 := by
  rw [full_centered_eq hn L hL]
  exact actual_activity_hs hn L hL

end AES8.PaperActivityFullCompression
