/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.WordMixThreeZeroFiber
import AES8.Reductions.Source.ThreeZeroResponseEnergy
import AES8.Estimates.FirstHigh.TwoZeroTwelveMoment
import AES8.Estimates.FirstHigh.FirstHighNine

/-!
# Actual first-high coordinate four from three-zero moments

The incoming-eleven centered block is exactly zero by the already admitted
old operator cap with L(4,11)=0. The other incoming components retain a
nonzero ORIGINAL source word, arbitrary affine source-coordinate permutations,
and the existing exact probability mixtures. One-coordinate information on
three-zero fibers supplies their moments before support projection and the
sharp one-residual channel damping. No conditional target cap is assumed.

  No local execution,
attacks, custom axioms, sorry, native_decide, predecessor or manuscript edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ActualFourMoment
open AESMixing AESMixing.AES AESConcrete
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component profile)
open AES8.ConditionalSourceResponse
open AES8.TwelveConditionalResponse
open AES8.TwelvePatternCoordinates (order order_zero order_ne_zero)
open AES8.OneSourceEventMoment (atomCap columnCap traceCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.TwoZeroTwelveMoment (constantCap)
open AES8.FirstHighSupportEvent (boundaryInput boundaryEventEnergy restrictSupport)

def thirteenFiberBudget : ℝ := atomCap ^ 2 * entryCap ^ 4 * columnCap * traceCap
def twelvePatternBudget : ℝ := atomCap ^ 2 * constantCap ^ 2 * entryCap ^ 2 * columnCap * traceCap

section Conditional
variable {G : Type*} [Fintype G]

theorem conditional_thirteen_energy_le (coords : G → WordState)
    (hinfo : Function.Bijective (fun g => coords g 0))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    (∑ g, conditionalResponse b k w (coords g) ^ 2) ≤ thirteenFiberBudget := by
  have h := ThreeZeroResponseEnergy.four_residual_energy_le
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (fun i => affineEquiv k w i) coords (wordLaw (sourceInput b k)) hinfo
    atomCap entryCap columnCap traceCap (by norm_num [columnCap, q])
    (by norm_num [traceCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun _ y x => TwoZeroThirteenMoment.residual_entry_le y x)
    (fun _ y => OneSourceEventMoment.residual_row_le y)
    OneSourceEventMoment.residual_trace_le
  change (∑ g, conditionalResponse b k w (coords g) ^ 2) ≤ thirteenFiberBudget at h
  exact h

theorem actual_thirteen_energy_le_of_source (coords : G → WordState)
    (hinfo : Function.Bijective (fun g => coords g 0))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) :
    (∑ g, component (error 1 b) 13 (coords g) ^ 2) ≤ thirteenFiberBudget := by
  rw [actual_component_thirteen_eq_probability_mixture b k]
  exact weighted_energy_le_uniform (conditionWeight b k)
    (fun w g => conditionalResponse b k w (coords g))
    (conditionWeight_nonnegative b k) (conditionWeight_total b k) thirteenFiberBudget
    (fun w => conditional_thirteen_energy_le coords hinfo b k hk w)

theorem conditional_twelve_pattern_energy_le (coords : G → WordState)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) (j : Fin 4)
    (hinfo : Function.Bijective (fun g => coords g (order j 1))) :
    (∑ g, conditionalPattern b k w j (coords g) ^ 2) ≤ twelvePatternBudget := by
  have h := ThreeZeroResponseEnergy.three_residual_constant_energy_le
    (fun i => patternChannel j (order j i))
    (fun i => affineEquiv k w (order j i))
    (fun g i => coords g (order j i)) (wordLaw (sourceInput b k)) hinfo
    atomCap constantCap entryCap columnCap traceCap (by norm_num [columnCap, q])
    (fun x => (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) x hk).le)
    (fun y x => by
      simpa only [order_zero, patternChannel, if_pos rfl, ite_true] using
        TwoZeroTwelveMoment.constant_entry_le y x)
    (fun y x => by
      simpa only [patternChannel, if_neg (order_ne_zero j 3 (by decide))] using
        TwoZeroThirteenMoment.residual_entry_le y x)
    (fun y => by
      simpa only [patternChannel, if_neg (order_ne_zero j 2 (by decide))] using
        OneSourceEventMoment.residual_row_le y)
    (by
      simpa only [patternChannel, if_neg (order_ne_zero j 1 (by decide))] using
        OneSourceEventMoment.residual_trace_le)
  calc
    _ = ∑ g, ZeroFiberResponseEnergy.response
        (fun i => patternChannel j (order j i))
        (fun i => affineEquiv k w (order j i))
        (fun g i => coords g (order j i)) (wordLaw (sourceInput b k)) g ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [TwoZeroTwelveMoment.conditionalPattern_eq_response]
    _ ≤ twelvePatternBudget := h

theorem conditional_twelve_energy_le (coords : G → WordState)
    (hinfo : ∀ j : Fin 4, Function.Bijective (fun g => coords g (order j 1)))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) (w : OtherAssignments k) :
    (∑ g, (∑ j : Fin 4, conditionalPattern b k w j (coords g)) ^ 2) ≤
      16 * twelvePatternBudget := by
  calc
    _ ≤ ∑ g, 4 * ∑ j : Fin 4, conditionalPattern b k w j (coords g) ^ 2 :=
      Finset.sum_le_sum (fun g _ => TwoZeroTwelveMoment.square_sum_four_le
        (fun j => conditionalPattern b k w j (coords g)))
    _ = 4 * ∑ j : Fin 4, ∑ g, conditionalPattern b k w j (coords g) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 4 * ∑ _j : Fin 4, twelvePatternBudget := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun j _ =>
        conditional_twelve_pattern_energy_le coords b k hk w j (hinfo j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]; ring

theorem actual_twelve_energy_le_of_source (coords : G → WordState)
    (hinfo : ∀ j : Fin 4, Function.Bijective (fun g => coords g (order j 1)))
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0) :
    (∑ g, component (error 1 b) 12 (coords g) ^ 2) ≤ 16 * twelvePatternBudget := by
  rw [actual_component_twelve_eq_probability_mixture b k]
  exact weighted_energy_le_uniform (conditionWeight b k)
    (fun w g => ∑ j : Fin 4, conditionalPattern b k w j (coords g))
    (conditionWeight_nonnegative b k) (conditionWeight_total b k) (16 * twelvePatternBudget)
    (fun w => conditional_twelve_energy_le coords hinfo b k hk w)

end Conditional

theorem actual_thirteen_zero_fiber_energy_le (r : Fin 16) (hr : maskSize r = 3)
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g : WordMixThreeZeroFiber.G r, component (error 1 b) 13 g.val ^ 2) ≤ thirteenFiberBudget := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  exact actual_thirteen_energy_le_of_source (fun g : WordMixThreeZeroFiber.G r => g.val)
    (WordMixThreeZeroFiber.coordinate_bijective r hr 0) b k hk

theorem actual_twelve_zero_fiber_energy_le (r : Fin 16) (hr : maskSize r = 3)
    (b : AES.State) (hb : b ≠ 0) :
    (∑ g : WordMixThreeZeroFiber.G r, component (error 1 b) 12 g.val ^ 2) ≤
      16 * twelvePatternBudget := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  exact actual_twelve_energy_le_of_source (fun g : WordMixThreeZeroFiber.G r => g.val)
    (fun j => WordMixThreeZeroFiber.coordinate_bijective r hr (order j 1)) b k hk

theorem actual_thirteen_event_energy_le (b : AES.State) (hb : b ≠ 0) :
    boundaryEventEnergy 1 (component (error 1 b) 13) ≤ 4 * thirteenFiberBudget := by
  calc
    _ ≤ ∑ j : Fin 4, ∑ g : WordMixThreeZeroFiber.G (WordMixThreeZeroFiber.zeroMask j),
        component (error 1 b) 13 g.val ^ 2 :=
      WordMixThreeZeroFiber.support_one_energy_le_zero_fibers _
    _ ≤ ∑ _j : Fin 4, thirteenFiberBudget := Finset.sum_le_sum (fun j _ =>
      actual_thirteen_zero_fiber_energy_le _ (WordMixThreeZeroFiber.zeroMask_size j) b hb)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]

theorem actual_twelve_event_energy_le (b : AES.State) (hb : b ≠ 0) :
    boundaryEventEnergy 1 (component (error 1 b) 12) ≤ 64 * twelvePatternBudget := by
  calc
    _ ≤ ∑ j : Fin 4, ∑ g : WordMixThreeZeroFiber.G (WordMixThreeZeroFiber.zeroMask j),
        component (error 1 b) 12 g.val ^ 2 :=
      WordMixThreeZeroFiber.support_one_energy_le_zero_fibers _
    _ ≤ ∑ _j : Fin 4, 16 * twelvePatternBudget := Finset.sum_le_sum (fun j _ =>
      actual_twelve_zero_fiber_energy_le _ (WordMixThreeZeroFiber.zeroMask_size j) b hb)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]; ring

theorem projected_energy_le_event (f : WordState → ℝ) :
    (∑ y, component (boundaryInput f) (4 : Fin 14) y ^ 2) ≤ boundaryEventEnergy 1 f := by
  have h := FirstHighSupportEvent.component_energy_le_restriction (boundaryInput f) (4 : Fin 14)
  change (∑ y, component (boundaryInput f) (4 : Fin 14) y ^ 2) ≤
    ∑ y, restrictSupport 1 (boundaryInput f) y ^ 2 at h
  rwa [FirstHighSupportEvent.restriction_energy_eq_boundaryEvent] at h

theorem exact_thirteen_scaled_budget :
    q ^ 5 * (4 * thirteenFiberBudget) = (145100800000 : ℝ) / q ^ 3 := by
  norm_num [thirteenFiberBudget, atomCap, entryCap, columnCap, traceCap, q]
theorem exact_twelve_scaled_budget :
    q ^ 5 * (64 * twelvePatternBudget) = (5804032000 : ℝ) / (q * (q - 1) ^ 2) := by
  norm_num [twelvePatternBudget, atomCap, constantCap, entryCap, columnCap, traceCap, q]

theorem thirteen_scaled_budget_le : q ^ 5 * (4 * thirteenFiberBudget) ≤
    (1 / 500000000 : ℝ) ^ 2 := by
  rw [exact_thirteen_scaled_budget]
  norm_num [q]
theorem twelve_scaled_budget_le : q ^ 5 * (64 * twelvePatternBudget) ≤
    (1 / 1000000000 : ℝ) ^ 2 := by
  rw [exact_twelve_scaled_budget]
  norm_num [q]

theorem actual_thirteen_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 13)) 4) ≤
      1 / 500000000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ) ^ 80) ^ 2 = q ^ 5 := by norm_num [q]
  rw [hs]
  exact (mul_le_mul_of_nonneg_left
    ((projected_energy_le_event _).trans (actual_thirteen_event_energy_le b hb))
    (by norm_num [q])).trans thirteen_scaled_budget_le

theorem actual_twelve_projected_length_le (b : AES.State) (hb : b ≠ 0) :
    (2 : ℝ) ^ 80 * l2 (component (boundaryInput (component (error 1 b) 12)) 4) ≤
      1 / 1000000000 := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (l2_nonneg _)) (by norm_num)).mp
  rw [mul_pow, l2_sq]
  have hs : ((2 : ℝ) ^ 80) ^ 2 = q ^ 5 := by norm_num [q]
  rw [hs]
  exact (mul_le_mul_of_nonneg_left
    ((projected_energy_le_event _).trans (actual_twelve_event_energy_le b hb))
    (by norm_num [q])).trans twelve_scaled_budget_le

end AES8.ActualFourMoment
