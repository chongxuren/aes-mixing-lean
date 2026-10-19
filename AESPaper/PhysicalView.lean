import AESMixing.PhysicalLawOps

/-!
Consequences of the physical retained-key identity: taking the maximum
over distinct inputs and identifying a finite adaptive transcript. These are
bridges for the final theorem, not assumed AES energy or mixing estimates.
-/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem action_differencePoint {V W : Type*} [Fintype V] [DecidableEq V]
    (K : W → V → ℝ) (a : V) : action K (differencePoint a) = fun b => K b a := by
  funext b
  simp [action, differencePoint, mul_ite]

namespace AES

theorem ordinaryDifferenceLaw_zero (n : ℕ) :
    ordinaryDifferenceLaw n 0 = differencePoint (0 : State) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ordinaryDifferenceLaw, ih, action_differencePoint]
    funext b
    rw [differenceChannel_zero_column]
    simp only [differencePoint, eq_comm]

theorem physicalDifferenceLaw_zero (r : ℕ) :
    physicalDifferenceLaw r 0 = differencePoint (0 : State) := by
  cases r with
  | zero => rfl
  | succ n =>
    simp only [physicalDifferenceLaw, ordinaryDifferenceLaw_zero, action_differencePoint]
    funext b
    rw [differenceChannel_zero_column]
    simp only [differencePoint, eq_comm]

theorem epsilon_lt_of_difference_bound (r : ℕ) (eps : ℝ) (heps : 0 < eps)
    (h : ∀ a : State, a ≠ 0 → tv (physicalDifferenceLaw r a) (uniformExcept 0) < eps) :
    epsilon r < eps := by
  unfold epsilon
  rw [Finset.sup'_lt_iff]
  intro x _
  by_cases hx : x.1 = x.2
  · simpa only [hx, if_true] using heps
  · rw [if_neg hx, physical_pair_tv]
    apply h
    intro hz
    exact hx (sub_eq_zero.mp hz).symm

def randomPermutationDifference (a : State) : State → ℝ :=
  if a = 0 then differencePoint 0 else uniformExcept 0

theorem physical_adaptive_difference (r : ℕ) (x : State) (choose : State → State) :
    retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) x choose =
      adaptiveDifferenceView (physicalDifferenceLaw r) (fun y => choose y-x) := by
  apply retained_adaptive_difference_identity
  intro z z' y
  exact congrFun (encrypt_pair_difference r z z') y

theorem physical_adaptive_tv_le (r : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (h : ∀ a : State, a ≠ 0 → tv (physicalDifferenceLaw r a) (uniformExcept 0) ≤ eps)
    (x : State) (choose : State → State) :
    tv (retainedAdaptiveLaw (encrypt r) (uniformKeyWeight (r+1)) x choose)
      (adaptiveDifferenceView randomPermutationDifference (fun y => choose y-x)) ≤ eps := by
  rw [physical_adaptive_difference]
  apply tv_adaptive_difference_le
  intro a
  by_cases ha : a = 0
  · subst a
    change tv (physicalDifferenceLaw r 0) (differencePoint 0) ≤ eps
    rw [physicalDifferenceLaw_zero]
    simpa only [tv, sub_self, abs_zero, Finset.sum_const_zero, zero_div] using heps
  · simpa only [randomPermutationDifference, if_neg ha] using h a ha

theorem ordinary_tv_eq_physical (n : ℕ) (a : State) :
    tv (ordinaryDifferenceLaw n a) (uniformExcept (0 : State)) =
      tv (physicalDifferenceLaw n a) (uniformExcept (0 : State)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have he : ordinaryDifferenceLaw (n+1) a =
        mixLaw (physicalDifferenceLaw (n+1) a) :=
      (ordinary_difference_action (ordinaryDifferenceLaw n a)).trans
        (congrArg mixLaw (final_difference_action (ordinaryDifferenceLaw n a))).symm
    dsimp only [mixLaw] at he
    calc
      tv (ordinaryDifferenceLaw (n+1) a) (uniformExcept (0 : State)) =
          tv (lawRelabel mixColumnsEquiv.toEquiv (physicalDifferenceLaw (n+1) a))
            (uniformExcept (0 : State)) :=
        congrArg (fun p : State → ℝ => tv p (uniformExcept (0 : State))) he
      _ = tv (physicalDifferenceLaw (n+1) a) (uniformExcept (0 : State)) :=
        tv_lawRelabel_uniformExcept mixColumnsEquiv.toEquiv 0 (map_zero mixColumnsEquiv) _

theorem physical_difference_tv_step (r : ℕ) (a : State) :
    tv (physicalDifferenceLaw (r+1) a) (uniformExcept (0 : State)) ≤
      tv (physicalDifferenceLaw r a) (uniformExcept (0 : State)) := by
  have h := tv_action_le (differenceChannel finalLayer) (differenceChannel_nonneg finalLayer)
    (differenceChannel_column finalLayer) (ordinaryDifferenceLaw r a) (uniformExcept (0 : State))
  rw [differenceChannel_stationary, ordinary_tv_eq_physical] at h
  exact h

end AES
end AESMixing
