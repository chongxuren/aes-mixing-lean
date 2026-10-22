/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.WordActivityFrame
import AES8.Reductions.Support.HighDegreeIdentity

/-!
# Exact shared-frame expansion of the middle high projection

Middle degree three has one omitted residual position c. Its activity
projection is reconstructed by the word frame and one shared inverse metric;
both negative cross terms remain. Middle degree four has no activity factor.
The final interface inserts this exact expansion between the two actual
centered steps defining highReturn, for arbitrary signed joint input.

This module supplies no marked graph/image equivalence or quantitative norm
cap. Constructive identities only; no attacks, manuscript or predecessor edits.

-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.MiddleFrameExpansion
open AESMixing
open AES8.WordActivityFrame (wordFrame wordInverse xi eta)

section Positions

/-- c is the sole activity position; the other three positions are residual. -/
def omittedMask (c : Fin 4) (i : Fin 4) : Bool := decide (i ≠ c)

-- Only the sixteen four-bit patterns and four position labels are checked.
-- No values of the underlying alphabet, words or AES states are enumerated.
private theorem omittedMask_degree : ∀ c : Fin 4,
    degreeIndex (omittedMask c) = 3 := by decide

private theorem omittedMask_injective : Function.Injective omittedMask := by decide

private theorem degree_three_position : ∀ a : Fin 4 → Bool,
    degreeIndex a = 3 → ∃ c : Fin 4, a = omittedMask c := by decide

private theorem degree_four_mask : ∀ a : Fin 4 → Bool,
    degreeIndex a = 4 ↔ a = fun _ => true := by decide

/-- Reindex the degree-three patterns by their unique activity position. -/
theorem degree_three_sum (F : (Fin 4 → Bool) → ℝ) :
    (∑ a : Fin 4 → Bool, if degreeIndex a = 3 then F a else 0) =
      ∑ c : Fin 4, F (omittedMask c) := by
  have hsplit (a : Fin 4 → Bool) :
      (if degreeIndex a = 3 then F a else 0) =
        ∑ c : Fin 4, if a = omittedMask c then F a else 0 := by
    by_cases ha : degreeIndex a = 3
    · obtain ⟨c, rfl⟩ := degree_three_position a ha
      simp [omittedMask_degree, omittedMask_injective.eq_iff]
    · have hne (c : Fin 4) : a ≠ omittedMask c := by
        intro he
        apply ha
        rw [he]
        exact omittedMask_degree c
      simp [ha, hne]
  calc
    _ = ∑ a : Fin 4 → Bool, ∑ c : Fin 4,
        if a = omittedMask c then F a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact hsplit a
    _ = ∑ c : Fin 4, ∑ a : Fin 4 → Bool,
        if a = omittedMask c then F a else 0 := Finset.sum_comm
    _ = _ := by simp

end Positions

section MiddleKernels
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The product of the three residual projection kernels outside c. -/
def residualTail (z : V) (c : Fin 4) (y x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, if i = c then 1 else residualProjection z (y i) (x i)

/-- The frame coefficient is external to this kernel, so it occurs once. -/
def frameAtom (z : V) (c : Fin 4) (s t : Bool) (y x : Fin 4 → V) : ℝ :=
  wordFrame z s (y c) * residualTail z c y x * wordFrame z t (x c)

/-- Degree four contains four residual factors and no activity metric. -/
def allResidualKernel (z : V) (y x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, residualProjection z (y i) (x i)

theorem omitted_projection (z : V) (c : Fin 4) (y x : Fin 4 → V) :
    productProjection z (omittedMask c) y x =
      activityMatrix z (y c) (x c) * residualTail z c y x := by
  fin_cases c <;>
    simp [productProjection, omittedMask, degreePiece, residualTail,
      Fin.prod_univ_four] <;> ring

/-- One activity coordinate uses one inverse metric between its two frames. -/
theorem omitted_projection_frame (z : V) (hV : 1 < Fintype.card V)
    (c : Fin 4) (y x : Fin 4 → V) :
    productProjection z (omittedMask c) y x =
      ∑ s : Bool, ∑ t : Bool, wordInverse V s t * frameAtom z c s t y x := by
  rw [omitted_projection, WordActivityFrame.word_projection z hV]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  unfold frameAtom
  ring

/-- The complete signed two-by-two inverse, including both cross terms. -/
theorem shared_inverse_sum (F : Bool → Bool → ℝ) :
    (∑ s : Bool, ∑ t : Bool, wordInverse V s t * F s t) =
      eta V * (F false false - xi V * F false true -
        xi V * F true false + F true true) := by
  simp [WordActivityFrame.wordInverse]
  ring

theorem omitted_projection_cross_terms (z : V) (hV : 1 < Fintype.card V)
    (c : Fin 4) (y x : Fin 4 → V) :
    productProjection z (omittedMask c) y x =
      eta V * (frameAtom z c false false y x -
        xi V * frameAtom z c false true y x -
        xi V * frameAtom z c true false y x +
        frameAtom z c true true y x) := by
  rw [omitted_projection_frame z hV]
  exact shared_inverse_sum (fun s t => frameAtom z c s t y x)

/-- Literal four-position degree-three decomposition before frame expansion. -/
theorem degree_three_positions (z : V) (y x : Fin 4 → V) :
    degreeKernel z 3 y x = ∑ c : Fin 4, productProjection z (omittedMask c) y x :=
  degree_three_sum (fun a => productProjection z a y x)

/-- Exact middle degree-three kernel, with one shared metric for each c. -/
theorem degree_three_kernel (z : V) (hV : 1 < Fintype.card V)
    (y x : Fin 4 → V) :
    degreeKernel z 3 y x =
      ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse V s t * frameAtom z c s t y x := by
  rw [degree_three_positions]
  exact Finset.sum_congr rfl (fun c _ => omitted_projection_frame z hV c y x)

theorem degree_four_kernel (z : V) : degreeKernel z 4 = allResidualKernel z := by
  funext y x
  simp [degreeKernel, degree_four_mask, productProjection, degreePiece, allResidualKernel]

/-- The expansion acts on the entire signed joint function, with no factorization. -/
theorem degree_three_action (z : V) (hV : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    degreeComponent z 3 f = fun y =>
      ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse V s t * action (frameAtom z c s t) f y := by
  rw [← degreeKernel_action]
  funext y
  unfold action
  simp_rw [degree_three_kernel z hV, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem degree_four_action (z : V) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z 4 f = action (allResidualKernel z) f := by
  rw [← degreeKernel_action, degree_four_kernel]

end MiddleKernels

section ActualCenteredReturn
open AESMixing.AES
open AES8.TransferAssembly (centeredStep highReturn)

private theorem centeredStep_scale (a : ℝ) (f : WordState → ℝ) :
    centeredStep (fun x => a * f x) = fun y => a * centeredStep f y := by
  funext y
  unfold TransferAssembly.centeredStep action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem centeredStep_shared_sum (F : Fin 4 → Bool → Bool → WordState → ℝ) :
    centeredStep (fun x => ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
      wordInverse AES.Word s t * F c s t x) =
      fun y => ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse AES.Word s t * centeredStep (F c s t) y := by
  rw [TransferAssembly.centeredStep_sum]
  funext y
  apply Finset.sum_congr rfl
  intro c _
  rw [TransferAssembly.centeredStep_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [TransferAssembly.centeredStep_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [centeredStep_scale]

/-- Kernel/action interface before distributing the outer centered step.
Both centered steps are actual fixed-kernel actions; no mass or zero-value
hypothesis is imposed on the arbitrary signed joint input. -/
theorem highReturn_eq_middle_frame (f : WordState → ℝ) :
    highReturn f = centeredStep
      ((fun y => ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
          wordInverse AES.Word s t *
            action (frameAtom (0 : AES.Word) c s t) (centeredStep f) y) +
        action (allResidualKernel (0 : AES.Word)) (centeredStep f)) := by
  rw [HighDegreeIdentity.highReturn_eq_centered_degree_sum,
    degree_three_action (0 : AES.Word) AESConcrete.AES.word_card_gt_one,
    degree_four_action]

/-- Downstream return interface: four omitted residual positions, two frame
labels on each side, and one shared signed inverse coefficient per term.
The full degree-four return follows with no activity coefficient. -/
theorem highReturn_eq_shared_frame_returns (f : WordState → ℝ) :
    highReturn f =
      (fun y => ∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse AES.Word s t *
          centeredStep
            (action (frameAtom (0 : AES.Word) c s t) (centeredStep f)) y) +
      centeredStep (action (allResidualKernel (0 : AES.Word)) (centeredStep f)) := by
  rw [highReturn_eq_middle_frame, TransferAssembly.centeredStep_add,
    centeredStep_shared_sum]

/-- Each fixed omitted-position return retains the two negative cross terms.
This exact signed identity precedes any triangle inequality or absolute cap. -/
theorem shared_frame_return_cross_terms (f : WordState → ℝ) (c : Fin 4)
    (y : WordState) :
    (∑ s : Bool, ∑ t : Bool, wordInverse AES.Word s t *
      centeredStep (action (frameAtom (0 : AES.Word) c s t) (centeredStep f)) y) =
      eta AES.Word *
        (centeredStep (action (frameAtom (0 : AES.Word) c false false) (centeredStep f)) y -
          xi AES.Word *
            centeredStep (action (frameAtom (0 : AES.Word) c false true) (centeredStep f)) y -
          xi AES.Word *
            centeredStep (action (frameAtom (0 : AES.Word) c true false) (centeredStep f)) y +
          centeredStep (action (frameAtom (0 : AES.Word) c true true) (centeredStep f)) y) :=
  shared_inverse_sum (fun s t =>
    centeredStep (action (frameAtom (0 : AES.Word) c s t) (centeredStep f)) y)

end ActualCenteredReturn
end AES8.MiddleFrameExpansion
